/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include <algorithm>
#include <atomic>
#include <climits>
#include <condition_variable>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <deque>
#include <functional>
#include <memory>
#include <mutex>
#include <string>
#include <string_view>
#include <system_error>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include <cerrno>
#include <fcntl.h>
#include <sys/stat.h>
#if defined(LEAN_MMAP) && !defined(LEAN_WINDOWS)
#include <sys/file.h>
#include <sys/mman.h>
#include <unistd.h>
#endif
// As in `library/module.cpp`: glibc before 2.28 does not define the flag, which kernels before 4.17
// ignore.
#if defined(__linux__) && !defined(MAP_FIXED_NOREPLACE)
#define MAP_FIXED_NOREPLACE 0x100000
#endif
#include "runtime/object.h"
#include "runtime/io.h"
#include "runtime/sstream.h"
#include "runtime/exception.h"
#include "runtime/compact.h"
#include "util/name.h"
#include "paperlean/olean_pack.h"
#include "paperlean/side_file.h"
#include "paperlean/fast_import.h"

namespace lean {
namespace {
// Closes its file descriptor.
class file_descriptor {
    int m_fd;
public:
    explicit file_descriptor(int fd) : m_fd(fd) {}
    file_descriptor(file_descriptor const &) = delete;
    file_descriptor & operator=(file_descriptor const &) = delete;
    ~file_descriptor() { if (m_fd != -1) close(m_fd); }
    int get() const { return m_fd; }
    operator bool() const { return m_fd != -1; }
};
}

// =======================================
// Olean packs
//
// A pack holds copies of many compacted-region files (`.olean`, `.olean.server`, `.olean.private`,
// `.ir.sig`, `.ir`), each relocated to where it lies in the pack, so that a process maps one file
// instead of tens of thousands. Packs named in `LEAN_OLEAN_PACK` are consulted by
// `lean_compacted_region_read`: a file below one of a pack's roots is served from the pack if no
// file of its chain (the parts of a module that point into one another) has changed since packing,
// judging by device, inode, size, mtime and ctime. A served region exposes the original file's
// `base_addr`, exactly like a file that could not be mapped at its base address and was relocated,
// so pointers into it from other regions are resolved and saved like those into the file's mapping.

namespace {
constexpr char g_pack_kind[] = "olean-pack";
// The header occupies the first page; regions start after it.
constexpr size_t g_pack_header_space = 4096;
// A `ModuleData` object: five object fields and `isModule`.
constexpr size_t g_module_data_size = sizeof(lean_ctor_object) + 5 * sizeof(void *) + sizeof(void *);

// The index (entries, chains, roots, strings) follows the regions and extends to the end of the
// file; the checksum covers the header and the index. The writer records the identity of the
// finished file (device, inode, size, modification and change times) in a small file next to the
// pack (`pack_identity`), and readers ignore a pack that no longer has it (`load_pack_core`), so that
// anything that writes to a pack, even restoring its modification time, stops its use. Readers check
// the header's own checksum and the checksums of the blocks of the index (`side_file_blocks`) when
// they first use a block, and the bounds of each entry of the index that they use, which the writer
// checks for all (`pack_tables::check_all`), so that a damaged entry is not used. As for `.olean`
// files under official Lean, nothing checks the bytes of the regions on use: reading them all takes
// too long (about 20% of the time of a large module, by the part of the pack it imports), so damage
// that leaves the file's metadata alone, such as a media error, is found only by `verify` (`paperlean
// status --verify`), which compares the checksums of the whole index and of the regions
// (`pack_payload_checksum`).
// The layout of the pack's index and tables; files of another layout are ignored.
constexpr uint32_t g_pack_format = 7;
// `pack_header::validated` of a pack whose writer checked its index.
constexpr uint32_t g_pack_validated = 0x564c4150;

struct pack_header {
    side_file_header common;
    uint32_t olean_flags;   // `olean_header::flags` every packed region has
    uint32_t format;        // `g_pack_format`
    uint64_t base_addr;     // address the whole file is mapped at
    uint64_t size;
    uint64_t entries_off, num_entries;
    uint64_t chains_off, num_chains;
    uint64_t roots_off, num_roots;   // roots are `pack_string`s
    uint64_t strings_off, strings_size;
    uint64_t modules_off, num_modules;
    uint64_t edges_off, num_edges;
    uint64_t parts_off;                  // one `pack_part` per entry
    uint64_t ext_entries_off, num_ext_entries;
    uint64_t ext_names_off, num_ext_names;
    uint64_t roots_hash_off, roots_hash_size;   // open addressing (root address, entry), 0 = empty
    // `[roots_area_off, names_off)`: copies of root objects (see the writer); `[names_off,
    // entries_off)`: the parts' name tables (`pack_part::names`). The regions end before both.
    uint64_t roots_area_off, names_off;
    // `pack_payload_checksum` of the bytes from the end of the header's page to the index.
    uint64_t payload_checksum;
    uint64_t paths_off, paths_size;   // `pack_path_slot`s: open addressing by `path_hash`
    uint64_t modules_by_hash_off;     // `num_modules` `pack_module_hash`es, sorted
    uint32_t validated;               // `g_pack_validated`
    uint32_t unused;
    // The checksums of the blocks of `[entries_off, block_sums_off)`, from `block_sums_off` to the end
    // of the file, and their checksum.
    uint64_t block_sums_off, block_sums_checksum;
    // `side_file_checksum` of the header with this field and `common.checksum` zero
    uint64_t header_checksum;
};

// The seed of the checksum of a table of block checksums.
constexpr uint64_t g_block_sums_seed = 0x73756d73ull;

// What the small file next to a pack records (`pack_identity_path`).
constexpr char g_pack_identity_kind[] = "pack-identity";
struct pack_identity {
    side_file_header common;   // `common.checksum`: `side_file_checksum` of this with the field zero
    uint64_t pack_checksum;    // `common.checksum` of the pack
    uint64_t dev, ino, size;
    int64_t mtime_sec, mtime_nsec, ctime_sec, ctime_nsec;
};

uint64_t pack_header_checksum(pack_header hdr) {
    hdr.common.checksum = 0;
    hdr.header_checksum = 0;
    return side_file_checksum(&hdr, sizeof(hdr));
}

// The slot of root address `a` in a hash table of `size` (a power of two) slots.
inline uint64_t root_slot(uint64_t a, uint64_t size) { return ((a >> 3) * 0x9e3779b97f4a7c15ull >> 20) & (size - 1); }

// The hash of the path `rel` below root `r`, for the paths table.
inline uint64_t path_hash(uint32_t r, std::string_view rel) {
    return side_file_checksum(rel.data(), rel.size(), 0x70617468ull + r);
}

static_assert(sizeof(pack_header) <= g_pack_header_space, "pack header must fit in its page");

uint64_t pack_checksum(pack_header hdr, char const * index, size_t index_size) {
    hdr.common.checksum = 0;
    return side_file_checksum(index, index_size, side_file_checksum(&hdr, sizeof(hdr)));
}

#if defined(LEAN_MMAP) && !defined(LEAN_WINDOWS)
// The bytes of a pack in `[g_pack_header_space, end)` are checksummed in blocks of this size (in
// parallel), and then the blocks' checksums.
constexpr uint64_t g_payload_block = uint64_t(1) << 20;

// Sets `sum` to that checksum of the pack open as `fd` whose index starts at `end`, reading the pack
// in blocks rather than mapping it: mapped pages count as the process's memory until they are
// unmapped, gigabytes for the pack of Mathlib's dependencies, which `prepare` writes while compilers
// run. Returns 0, or the `errno` of a read that failed.
int pack_payload_checksum(int fd, uint64_t end, uint64_t & sum) {
    uint64_t from = g_pack_header_space;
    size_t n = end > from ? (end - from + g_payload_block - 1) / g_payload_block : 0;
    std::vector<uint64_t> sums(n);
    std::atomic<size_t> next{0};
    std::atomic<int> error{0};
    auto work = [&]() {
        std::vector<char> buf(g_payload_block);
        for (size_t i; error == 0 && (i = next.fetch_add(1)) < n;) {
            uint64_t b = from + i * g_payload_block;
            size_t len = std::min(g_payload_block, end - b);
            for (size_t got = 0; got < len;) {
                ssize_t r = pread(fd, buf.data() + got, len - got, b + got);
                if (r < 0 && errno == EINTR) continue;
                if (r <= 0) { error = r < 0 ? errno : EIO; return; }
                got += r;
            }
            sums[i] = side_file_checksum(buf.data(), len, i);
        }
    };
    unsigned workers = std::max(1u, std::min(8u, std::thread::hardware_concurrency()));
    std::vector<std::thread> threads;
    try {
        for (unsigned t = 1; t < workers && t < n; t++) threads.emplace_back(work);
    } catch (std::system_error &) {}
    work();
    for (std::thread & t : threads) t.join();
    sum = side_file_checksum(sums.data(), sums.size() * sizeof(uint64_t));
    return error;
}
#endif

struct pack_string { uint64_t off, len; };

struct pack_entry {
    uint64_t offset, size;   // the region's copy of its file within the pack
    uint64_t orig_base;      // `olean_header::base_addr` of the file
    uint64_t root;           // root object, at its address in the mapped pack
    uint64_t dev, ino;
    int64_t mtime_sec, mtime_nsec, ctime_sec, ctime_nsec;
    pack_string path;        // relative to its root
    uint32_t root_idx, chain, part, flags;
    // The root that the root slot of the region holds: in its own or an earlier region of the chain,
    // as a `CompactedRegion`'s root must be (embedding it in a snapshot relocates it), unlike its copy
    // in the roots area (`root`).
    uint64_t region_root;
};
// The githash of the file's header is the writer's `LEAN_GITHASH`, which is the reader's.
constexpr uint32_t entry_githash_match = 1;

struct pack_chain { uint32_t first, count; };

// A slot of the paths table: the entry with that path, + 1 (0 = empty), and the high half of its hash.
struct pack_path_slot { uint32_t entry, tag; };
// A module by the hash of its name.
struct pack_module_hash { uint64_t hash; uint32_t module, unused; };

// A module of the pack: its `.olean` and IR chains, and the imports of its `.olean` files.
struct pack_module {
    pack_string stem;       // path of its files relative to its root, without extension
    uint64_t name_hash;     // `Name.hash` of its name
    uint32_t root_idx;
    int32_t olean_chain;    // -1 if not packed
    int32_t ir_chain;       // -1 if not packed
    uint32_t first_edge, num_edges;
    uint32_t flags;         // `pack_module_*`
};
// `ModuleData.isModule` of its `.olean`
constexpr uint32_t pack_module_is_module = 1;
// Its edges are the imports of every part of its `.olean` chain, which share their `imports`.
constexpr uint32_t pack_module_edges = 2;

// An import of a module, as in `Import`.
struct pack_edge {
    uint64_t module;        // the imported module's `Name` object in the `Import`, in the pack
    int32_t target;         // the imported module, -1 if it is not in the pack
    uint8_t import_all, is_exported, is_meta, unused;
};

// What `finalizeImport` reads from the root `ModuleData` of a packed part, so that it need not read
// the root.
struct pack_part {
    uint64_t const_names, constants, extra_const_names, entries;   // the arrays' addresses
    uint32_t num_const_names, num_constants, num_extra_const_names, num_entries;
    uint32_t first_ext;     // the elements of `entries`, as `pack_ext_entry`s from here
    uint32_t is_module;     // `ModuleData.isModule`
    // File offset of the name table: the hash of each name of `constNames` and then of
    // `extraConstNames`, then one bit per name (in 64-bit words) that is set if the pack has no other
    // occurrence of the hash, except in the same array of another part of the same module.
    uint64_t names;
    uint64_t names_checksum;   // `side_file_checksum` of the name table
};

inline uint64_t part_names_size(pack_part const & pp) {
    uint64_t n = static_cast<uint64_t>(pp.num_const_names) + pp.num_extra_const_names;
    return 8 * n + 8 * ((n + 63) / 64);
}

// An element of `ModuleData.entries`: an extension name and that extension's entries.
struct pack_ext_entry {
    uint64_t entries;       // address of the entries array
    uint32_t name;          // index into the table of extension names
    uint32_t unused;
};

// An extension name of the pack: one of its `Name` objects in the pack.
struct pack_ext_name {
    uint64_t name;
};

// Runtime layout of `ModuleData` (object fields, then the scalar `isModule`) and `Import`.
constexpr unsigned g_module_data_imports = 0;
constexpr unsigned g_module_data_num_objs = 5;
inline bool module_data_is_module(object * d) { return lean_ctor_get_uint8(d, sizeof(void *) * g_module_data_num_objs) != 0; }
inline object * module_data_imports(object * d) { return lean_ctor_get(d, g_module_data_imports); }
inline object * module_data_field(object * d, unsigned i) { return lean_ctor_get(d, i); }
inline uint8_t import_flag(object * i, unsigned k) { return lean_ctor_get_uint8(i, sizeof(void *) + k); }

#if defined(LEAN_MMAP) && !defined(LEAN_WINDOWS)
void set_file_id(pack_entry & e, struct stat const & st) {
    e.dev = st.st_dev; e.ino = st.st_ino; e.size = st.st_size;
    e.mtime_sec = LEAN_STAT_MTIM(st).tv_sec; e.mtime_nsec = LEAN_STAT_MTIM(st).tv_nsec;
    e.ctime_sec = LEAN_STAT_CTIM(st).tv_sec; e.ctime_nsec = LEAN_STAT_CTIM(st).tv_nsec;
}

bool same_file_id(pack_entry const & e, struct stat const & st) {
    return e.dev == static_cast<uint64_t>(st.st_dev) && e.ino == static_cast<uint64_t>(st.st_ino) &&
        e.size == static_cast<uint64_t>(st.st_size) &&
        e.mtime_sec == LEAN_STAT_MTIM(st).tv_sec && e.mtime_nsec == LEAN_STAT_MTIM(st).tv_nsec &&
        e.ctime_sec == LEAN_STAT_CTIM(st).tv_sec && e.ctime_nsec == LEAN_STAT_CTIM(st).tv_nsec;
}

// Whether `a` and `b` are the same file, unchanged.
bool same_stat(struct stat const & a, struct stat const & b) {
    pack_entry e = {};
    set_file_id(e, a);
    return same_file_id(e, b);
}
#endif

size_t align_up(size_t n, size_t a) { return (n + a - 1) & ~(a - 1); }

// The path of the files of module `n` relative to their root, without extension, as `modToFilePath`
// builds it; false if `n` has a numeric component.
bool module_stem(b_obj_arg n, std::string & stem) {
    if (lean_is_scalar(n)) { stem.clear(); return true; }
    if (lean_ptr_tag(n) != 1 || !module_stem(lean_ctor_get(n, 0), stem)) return false;
    object * c = lean_ctor_get(n, 1);
    // the stem must determine the name
    if (memchr(lean_string_cstr(c), '/', lean_string_size(c) - 1)) return false;
    if (!stem.empty()) stem += '/';
    stem += lean_string_cstr(c);
    return true;
}

// A string that identifies `n` exactly: its components, strings and numbers marked apart, each string
// after its length, as a string can hold any bytes.
void ext_name_key(b_obj_arg n, std::string & key) {
    if (lean_is_scalar(n)) { key.clear(); return; }
    ext_name_key(lean_ctor_get(n, 0), key);
    object * c = lean_ctor_get(n, 1);
    if (lean_ptr_tag(n) == 1) {
        size_t len = lean_string_size(c) - 1;
        key += 's';
        key += std::to_string(len);
        key += ':';
        key.append(lean_string_cstr(c), len);
    } else {
        key += 'n';
        if (lean_is_scalar(c)) {
            key += std::to_string(lean_unbox(c));
        } else {
            std::ostringstream out;
            out << mpz_value(c);
            key += out.str();
        }
        key += ':';
    }
}

bool ends_with(std::string const & s, char const * suffix, std::string & prefix) {
    size_t n = strlen(suffix);
    if (s.size() < n || s.compare(s.size() - n, n, suffix) != 0) return false;
    prefix = s.substr(0, s.size() - n);
    return true;
}

// The tables of a pack, given its header and its index (the bytes from `entries_off` to the end).
// Readers check an entry of a table when they first use it (`entry_ok`, `chain_ok`, ...): the
// checksums of the blocks it lies in (`blocks`), and its bounds, so that nothing is read out of bounds;
// the writer and `verify` check all of them and the relations between them (`check_all`).
struct pack_tables {
    pack_header hdr;
    uint64_t page = 0;
    // the index's blocks, or none if the whole index is checked otherwise
    side_file_blocks const * blocks = nullptr;
    pack_entry const * entries = nullptr;
    pack_chain const * chains = nullptr;
    pack_string const * root_strings = nullptr;
    char const * strings = nullptr;
    pack_module const * modules = nullptr;
    pack_edge const * edges = nullptr;
    pack_part const * parts = nullptr;
    pack_ext_entry const * ext_entries = nullptr;
    pack_ext_name const * ext_names = nullptr;
    std::pair<uint64_t, uint64_t> const * roots_hash = nullptr;
    pack_path_slot const * paths = nullptr;
    pack_module_hash const * modules_by_hash = nullptr;

    static bool in_range(uint64_t off, uint64_t len, uint64_t from, uint64_t to) {
        return off >= from && off <= to && len <= to - off;
    }
    // Sets the header; whether the offsets and sizes of the file's areas and tables are in range.
    bool init_header(pack_header const & h) {
        hdr = h;
        page = static_cast<uint64_t>(sysconf(_SC_PAGESIZE));
        if (hdr.entries_off < g_pack_header_space || hdr.entries_off > hdr.size || hdr.entries_off % 64 != 0 ||
            hdr.roots_area_off < g_pack_header_space || hdr.roots_area_off % 64 != 0 ||
            hdr.names_off < hdr.roots_area_off || hdr.names_off % 64 != 0 || hdr.names_off > hdr.entries_off ||
            hdr.base_addr % page != 0 || hdr.base_addr > UINTPTR_MAX - hdr.size ||
            hdr.block_sums_off % 8 != 0 || hdr.block_sums_off < hdr.entries_off || hdr.block_sums_off > hdr.size ||
            hdr.size - hdr.block_sums_off != 8 * side_file_num_blocks(hdr.block_sums_off - hdr.entries_off))
            return false;
        // the tables lie in the blocks
        uint64_t end = hdr.block_sums_off;
        auto in_index = [&](uint64_t off, uint64_t n, uint64_t elem) {
            return off % 8 == 0 && n <= UINT32_MAX && n <= hdr.size / elem &&
                in_range(off, n * elem, hdr.entries_off, end);
        };
        auto pow2 = [](uint64_t n) { return n != 0 && (n & (n - 1)) == 0; };
        // module ids hold the module index in 24 bits
        return in_index(hdr.entries_off, hdr.num_entries, sizeof(pack_entry)) &&
            in_index(hdr.chains_off, hdr.num_chains, sizeof(pack_chain)) &&
            in_index(hdr.roots_off, hdr.num_roots, sizeof(pack_string)) &&
            in_range(hdr.strings_off, hdr.strings_size, hdr.entries_off, end) &&
            in_index(hdr.modules_off, hdr.num_modules, sizeof(pack_module)) && hdr.num_modules <= 0xffffff &&
            in_index(hdr.edges_off, hdr.num_edges, sizeof(pack_edge)) &&
            in_index(hdr.parts_off, hdr.num_entries, sizeof(pack_part)) &&
            in_index(hdr.ext_entries_off, hdr.num_ext_entries, sizeof(pack_ext_entry)) &&
            in_index(hdr.ext_names_off, hdr.num_ext_names, sizeof(pack_ext_name)) &&
            pow2(hdr.roots_hash_size) && in_index(hdr.roots_hash_off, hdr.roots_hash_size, 2 * sizeof(uint64_t)) &&
            pow2(hdr.paths_size) && in_index(hdr.paths_off, hdr.paths_size, sizeof(pack_path_slot)) &&
            in_index(hdr.modules_by_hash_off, hdr.num_modules, sizeof(pack_module_hash));
    }
    // Sets the tables, after `init_header`, from the index at `index`.
    void set_tables(char const * index) {
        auto at = [&](uint64_t off) { return index + (off - hdr.entries_off); };
        entries = reinterpret_cast<pack_entry const *>(at(hdr.entries_off));
        chains = reinterpret_cast<pack_chain const *>(at(hdr.chains_off));
        root_strings = reinterpret_cast<pack_string const *>(at(hdr.roots_off));
        strings = at(hdr.strings_off);
        modules = reinterpret_cast<pack_module const *>(at(hdr.modules_off));
        edges = reinterpret_cast<pack_edge const *>(at(hdr.edges_off));
        parts = reinterpret_cast<pack_part const *>(at(hdr.parts_off));
        ext_entries = reinterpret_cast<pack_ext_entry const *>(at(hdr.ext_entries_off));
        ext_names = reinterpret_cast<pack_ext_name const *>(at(hdr.ext_names_off));
        roots_hash = reinterpret_cast<std::pair<uint64_t, uint64_t> const *>(at(hdr.roots_hash_off));
        paths = reinterpret_cast<pack_path_slot const *>(at(hdr.paths_off));
        modules_by_hash = reinterpret_cast<pack_module_hash const *>(at(hdr.modules_by_hash_off));
    }

    // Whether the `n` bytes at `p`, of a table, are as written.
    bool used(void const * p, uint64_t n) const { return !blocks || blocks->ok(p, n); }
    template<class T> bool used(T const & x) const { return used(&x, sizeof(T)); }
    bool valid_str(pack_string s) const { return in_range(s.off, s.len, 0, hdr.strings_size) && used(strings + s.off, s.len); }
    std::string_view str(pack_string s) const { return std::string_view(strings + s.off, s.len); }
    // An object of the pack's regions.
    bool in_regions(uint64_t a) const {
        return a % sizeof(void *) == 0 && a >= hdr.base_addr + g_pack_header_space && a < hdr.base_addr + hdr.roots_area_off;
    }
    // A copy of a root object in the roots area.
    bool in_roots_area(uint64_t a) const {
        return a % sizeof(void *) == 0 && a >= hdr.base_addr + hdr.roots_area_off &&
            a <= hdr.base_addr + hdr.names_off - g_module_data_size;
    }

    // Whether entry `i` is part `part` of its chain, its region lies after the previous one and holds
    // at least a header and the root slot, and its roots lie in the data of its own or an earlier
    // region of the chain, or (`root`) in the roots area.
    bool entry_ok(uint64_t i) const {
        if (i >= hdr.num_entries || !used(entries[i])) return false;
        pack_entry const & e = entries[i];
        if (e.root_idx >= hdr.num_roots || e.chain >= hdr.num_chains || !valid_str(e.path) ||
            (e.flags & ~entry_githash_match) != 0 || !used(chains[e.chain]))
            return false;
        pack_chain const & c = chains[e.chain];
        if (e.part >= c.count || static_cast<uint64_t>(c.first) + e.part != i || !used(entries[c.first])) return false;
        uint64_t region_end = g_pack_header_space;
        if (i > 0) {
            pack_entry const & prev = entries[i - 1];
            if (!used(prev) || !in_range(prev.offset, prev.size, g_pack_header_space, hdr.roots_area_off)) return false;
            region_end = prev.offset + prev.size;
        }
        if (e.offset % 64 != 0 || e.offset < region_end || e.size < olean_header_size() + sizeof(size_t) ||
            !in_range(e.offset, e.size, g_pack_header_space, hdr.roots_area_off) ||
            e.orig_base % page != 0 || e.orig_base > UINTPTR_MAX - e.size)
            return false;
        uint64_t first = entries[c.first].offset;
        auto in_chain = [&](uint64_t a) {
            return a % sizeof(void *) == 0 && a >= hdr.base_addr + first + olean_header_size() &&
                a < hdr.base_addr + e.offset + e.size;
        };
        return in_chain(e.region_root) && (in_chain(e.root) || in_roots_area(e.root));
    }
    // Whether chain `c` and its entries are consistent.
    bool chain_ok(uint64_t c) const {
        if (c >= hdr.num_chains || !used(chains[c])) return false;
        pack_chain const & ch = chains[c];
        if (ch.count == 0 || ch.first >= hdr.num_entries || ch.count > hdr.num_entries - ch.first) return false;
        for (uint64_t i = ch.first; i < static_cast<uint64_t>(ch.first) + ch.count; i++)
            if (!entry_ok(i) || entries[i].chain != c) return false;
        return true;
    }
    bool edge_ok(uint64_t j) const {
        pack_edge const & e = edges[j];
        return used(e) && e.target >= -1 && (e.target < 0 || static_cast<uint64_t>(e.target) < hdr.num_modules) && in_regions(e.module);
    }
    // Whether module `i`, its chains and its edges are consistent.
    bool module_ok(uint64_t i) const {
        if (i >= hdr.num_modules || !used(modules[i])) return false;
        pack_module const & m = modules[i];
        auto valid_chain = [&](int32_t c) {
            return c == -1 || (c >= 0 && chain_ok(static_cast<uint64_t>(c)) && entries[chains[c].first].root_idx == m.root_idx);
        };
        if (!valid_str(m.stem) || m.root_idx >= hdr.num_roots || !valid_chain(m.olean_chain) || !valid_chain(m.ir_chain) ||
            (m.flags & ~(pack_module_is_module | pack_module_edges)) != 0 ||
            m.first_edge > hdr.num_edges || m.num_edges > hdr.num_edges - m.first_edge ||
            ((m.flags & pack_module_edges) && m.olean_chain == -1))
            return false;
        for (uint64_t j = m.first_edge; j < static_cast<uint64_t>(m.first_edge) + m.num_edges; j++)
            if (!edge_ok(j)) return false;
        return true;
    }
    bool ext_entry_ok(uint64_t j) const {
        pack_ext_entry const & ee = ext_entries[j];
        return used(ee) && in_regions(ee.entries) && ee.name < hdr.num_ext_names && used(ext_names[ee.name]) &&
            in_regions(ext_names[ee.name].name);
    }
    // Whether the part of entry `i`, its extension entries and their names are consistent.
    bool part_ok(uint64_t i) const {
        if (i >= hdr.num_entries || !used(parts[i])) return false;
        pack_part const & pp = parts[i];
        if (!in_regions(pp.const_names) || !in_regions(pp.constants) || !in_regions(pp.extra_const_names) ||
            !in_regions(pp.entries) || pp.first_ext > hdr.num_ext_entries ||
            pp.num_entries > hdr.num_ext_entries - pp.first_ext || pp.is_module > 1 ||
            pp.names % 8 != 0 || !in_range(pp.names, part_names_size(pp), hdr.names_off, hdr.entries_off))
            return false;
        for (uint64_t j = pp.first_ext; j < static_cast<uint64_t>(pp.first_ext) + pp.num_entries; j++)
            if (!ext_entry_ok(j)) return false;
        return true;
    }

    // The entry whose part has its root object at `a`: -1 if none, -2 if the table is damaged.
    int64_t find_root(uint64_t a) const {
        uint64_t size = hdr.roots_hash_size;
        uint64_t slot = root_slot(a, size);
        for (uint64_t n = 0; n < size; n++, slot = (slot + 1) & (size - 1)) {
            if (!used(roots_hash[slot])) return -2;
            if (roots_hash[slot].first == 0) return -1;
            if (roots_hash[slot].first != a) continue;
            uint64_t i = roots_hash[slot].second;
            return i < hdr.num_entries && used(entries[i]) && entries[i].root == a ? static_cast<int64_t>(i) : -2;
        }
        // no empty slot
        return -2;
    }
    // The entry of the file `rel` below root `r`: -1 if none, -2 if the table is damaged.
    int64_t find_path(uint32_t r, std::string_view rel) const {
        uint64_t h = path_hash(r, rel), size = hdr.paths_size;
        uint32_t tag = static_cast<uint32_t>(h >> 32);
        uint64_t slot = h & (size - 1);
        for (uint64_t n = 0; n < size; n++, slot = (slot + 1) & (size - 1)) {
            pack_path_slot const & s = paths[slot];
            if (!used(s)) return -2;
            if (s.entry == 0) return -1;
            if (s.entry > hdr.num_entries) return -2;
            if (s.tag != tag) continue;
            pack_entry const & e = entries[s.entry - 1];
            if (!used(e)) return -2;
            if (e.root_idx == r && valid_str(e.path) && str(e.path) == rel) return s.entry - 1;
        }
        // no empty slot
        return -2;
    }
    // The first element of `modules_by_hash` whose hash is not below `h`; `hdr.num_modules` if
    // there is none or the table is damaged, which sets `damaged`.
    uint64_t first_module_with_hash(uint64_t h, bool & damaged) const {
        uint64_t lo = 0, hi = hdr.num_modules;
        while (lo < hi) {
            uint64_t mid = lo + (hi - lo) / 2;
            if (!used(modules_by_hash[mid])) { damaged = true; return hdr.num_modules; }
            if (modules_by_hash[mid].hash < h) lo = mid + 1; else hi = mid;
        }
        return lo;
    }

    // Why the tables are not as their writer leaves them, if they are not: every entry is
    // consistent, the chains partition the entries in order, and the hash tables find every entry
    // and module.
    char const * check_all() const {
        uint64_t next = 0;
        for (uint64_t c = 0; c < hdr.num_chains; c++) {
            if (chains[c].first != next || !chain_ok(c)) return "corrupt (chains)";
            next += chains[c].count;
        }
        if (next != hdr.num_entries) return "corrupt (chains)";
        for (uint64_t r = 0; r < hdr.num_roots; r++)
            if (!valid_str(root_strings[r])) return "corrupt (roots)";
        for (uint64_t m = 0; m < hdr.num_modules; m++)
            if (!module_ok(m)) return "corrupt (modules)";
        for (uint64_t j = 0; j < hdr.num_edges; j++)
            if (!edge_ok(j)) return "corrupt (imports)";
        for (uint64_t i = 0; i < hdr.num_entries; i++)
            if (!part_ok(i)) return "corrupt (module data)";
        for (uint64_t j = 0; j < hdr.num_ext_entries; j++)
            if (!ext_entry_ok(j)) return "corrupt (extension entries)";
        for (uint64_t k = 0; k < hdr.num_ext_names; k++)
            if (!in_regions(ext_names[k].name)) return "corrupt (extension names)";
        // every slot is empty or holds its entry, and some slot is empty, which ends probes
        bool empty = false;
        for (uint64_t s = 0; s < hdr.roots_hash_size; s++) {
            if (roots_hash[s].first == 0) { empty = true; continue; }
            if (roots_hash[s].second >= hdr.num_entries || entries[roots_hash[s].second].root != roots_hash[s].first)
                return "corrupt (roots table)";
        }
        if (!empty) return "corrupt (roots table)";
        empty = false;
        for (uint64_t s = 0; s < hdr.paths_size; s++) {
            if (paths[s].entry == 0) empty = true;
            else if (paths[s].entry > hdr.num_entries) return "corrupt (paths table)";
        }
        if (!empty) return "corrupt (paths table)";
        for (uint64_t i = 0; i < hdr.num_entries; i++) {
            if (find_root(entries[i].root) < 0) return "corrupt (roots table)";
            if (find_path(entries[i].root_idx, str(entries[i].path)) != static_cast<int64_t>(i)) return "corrupt (paths table)";
        }
        // every module once, by hash and then index
        for (uint64_t k = 0; k < hdr.num_modules; k++) {
            pack_module_hash const & mh = modules_by_hash[k];
            if (mh.module >= hdr.num_modules || mh.hash != modules[mh.module].name_hash ||
                (k > 0 && (modules_by_hash[k - 1].hash > mh.hash ||
                           (modules_by_hash[k - 1].hash == mh.hash && modules_by_hash[k - 1].module >= mh.module))))
                return "corrupt (modules table)";
        }
        return nullptr;
    }
};

struct loaded_pack : pack_tables {
    std::string fname;
    char * begin = nullptr;
    std::vector<std::string> roots;
    // the current descriptors of `roots`, negative if one cannot be opened
    std::unique_ptr<std::atomic<int>[]> root_fds;
    // per chain: the generation of the imports (`g_pack_generation`) it was checked for << 2 | 0 = not
    // yet checked, 1 = unchanged, 2 = changed or damaged, 3 = being checked
    std::unique_ptr<std::atomic<uint32_t>[]> chain_state;
    // per module: 0 = not yet known, else `module_known` and the other `module_*` bits that hold
    std::unique_ptr<std::atomic<uint8_t>[]> module_state;
    // per part: 0 = not yet checked, 1 = consistent, 2 = damaged
    std::unique_ptr<std::atomic<uint8_t>[]> part_state;
    // per part: 0 = name table not yet checked, 1 = valid, 2 = invalid
    std::unique_ptr<std::atomic<uint8_t>[]> names_state;
    std::unique_ptr<std::atomic<bool>> warned;
    std::unique_ptr<side_file_blocks> block_table;

    // Reports, once, that an entry of the index is damaged; it is not used.
    void damaged() const {
        if (!warned->exchange(true))
            side_file_warning("warning: olean pack '%s': ignoring damaged entries of its index\n", fname.c_str());
    }
};
constexpr uint8_t module_known = 1;
// the module, its chains and its edges are consistent
constexpr uint8_t module_valid = 2;
// reading its files serves them from this pack, as `find_in_packs` picks the pack and root by the
// first root that is a prefix of a file's path
constexpr uint8_t module_here = 4;

// Set once, after all packs are loaded.
std::atomic<std::vector<loaded_pack> *> g_packs{nullptr};
// Incremented by each import after the packs are loaded (`lean_paperlean_pack_next_import`): each
// import checks again whether the files of the chains it uses changed, as Lean reads them again.
std::atomic<uint32_t> g_pack_generation{0};
std::once_flag g_packs_once;
std::atomic<size_t> g_pack_served{0};
std::atomic<size_t> g_pack_not_served{0};
// The number of times a chain was found changed.
std::atomic<size_t> g_changed_chains{0};

#if defined(LEAN_MMAP) && !defined(LEAN_WINDOWS)
/*
A root that the pack records as `^N/rest` is relative to the directory of the pack file: `N` trailing
components of that directory are dropped and `/rest` is appended as it is, so that a root recorded
for a project's directory keeps the spelling of the paths Lean reads (as in `LEAN_PATH`) when the
project moves.
*/
std::string resolve_root(std::string const & pack_file, std::string const & root) {
    if (root.size() < 3 || root[0] != '^') return root;
    size_t slash = root.find('/');
    if (slash == std::string::npos || slash == 1) return root;
    unsigned n = 0;
    for (size_t i = 1; i < slash; i++) {
        if (root[i] < '0' || root[i] > '9' || n > 1000) return root;
        n = n * 10 + (root[i] - '0');
    }
    std::string dir = pack_file.substr(0, pack_file.rfind('/'));
    for (unsigned i = 0; i < n && dir.find('/') != std::string::npos; i++) dir = dir.substr(0, dir.rfind('/'));
    return dir + root.substr(slash);
}

// A descriptor of the directory `r`, shared by all packs with that root (a build writes many), open
// for the whole process and not passed to child processes; negative, with the error in `error`, if
// `r` cannot be opened. With `again`, one that is no longer the directory at `r` is replaced (it stays
// open, as other threads may be using it, so a process holds one more per replacement).
int root_dir_fd(std::string const & r, int & error, bool again = false) {
    static std::mutex mutex;
    static std::unordered_map<std::string, int> fds;
    std::lock_guard<std::mutex> lock(mutex);
    auto it = fds.find(r);
    if (it != fds.end()) {
        struct stat at_path, open_dir;
        if (!again || (stat(r.c_str(), &at_path) == 0 && fstat(it->second, &open_dir) == 0 &&
                       at_path.st_dev == open_dir.st_dev && at_path.st_ino == open_dir.st_ino))
            return it->second;
    }
    int fd = open(r.c_str(), O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    error = fd < 0 ? errno : 0;
    if (fd >= 0) fds[r] = fd;
    else if (it != fds.end()) fds.erase(it);
    return fd;
}

// The file next to the pack `pack` that records its identity (`pack_identity`): a `*.paperlean` file
// that the names of packs (`lib-*`, `pack-*`, ...) do not match.
std::string pack_identity_path(std::string const & pack) {
    size_t slash = pack.rfind('/');
    size_t name = slash == std::string::npos ? 0 : slash + 1;
    std::string file = pack.substr(name);
    if (file.size() < 10 || file.compare(file.size() - 10, 10, ".paperlean") != 0) file += ".paperlean";
    return pack.substr(0, name) + "id-" + file;
}

uint64_t pack_identity_checksum(pack_identity id) {
    id.common.checksum = 0;
    return side_file_checksum(&id, sizeof(id));
}

// Whether the file `st` is the pack with `checksum` that its identity file describes.
bool pack_identity_ok(std::string const & pack, uint64_t checksum, struct stat const & st) {
    file_descriptor fd(open(pack_identity_path(pack).c_str(), O_RDONLY | O_CLOEXEC | O_NONBLOCK));
    struct stat id_st;
    pack_identity id;
    if (!fd || fstat(fd.get(), &id_st) != 0 || !S_ISREG(id_st.st_mode) ||
        pread(fd.get(), &id, sizeof(id), 0) != static_cast<ssize_t>(sizeof(id)) ||
        check_side_file_header(id.common, g_pack_identity_kind, sizeof(pack_identity)) ||
        pack_identity_checksum(id) != id.common.checksum || id.pack_checksum != checksum)
        return false;
    pack_entry e = {};
    e.dev = id.dev; e.ino = id.ino; e.size = id.size;
    e.mtime_sec = id.mtime_sec; e.mtime_nsec = id.mtime_nsec;
    e.ctime_sec = id.ctime_sec; e.ctime_nsec = id.ctime_nsec;
    return same_file_id(e, st);
}

// Records the identity of the pack `pack`, as a file renamed into place.
void write_pack_identity(std::string const & pack, uint64_t checksum, bool sync) {
    struct stat st;
    if (stat(pack.c_str(), &st) != 0)
        throw exception((sstream() << "failed to read '" << pack << "': " << strerror(errno)).str());
    pack_entry e = {};
    set_file_id(e, st);
    pack_identity id;
    memset(&id, 0, sizeof(id));
    init_side_file_header(id.common, g_pack_identity_kind, sizeof(pack_identity));
    id.pack_checksum = checksum;
    id.dev = e.dev; id.ino = e.ino; id.size = e.size;
    id.mtime_sec = e.mtime_sec; id.mtime_nsec = e.mtime_nsec;
    id.ctime_sec = e.ctime_sec; id.ctime_nsec = e.ctime_nsec;
    id.common.checksum = pack_identity_checksum(id);
    std::string out = pack_identity_path(pack);
    std::string tmp = out + ".tmp." + std::to_string(getpid());
    std::remove(tmp.c_str());
    file_descriptor fd(open(tmp.c_str(), O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, 0444));
    bool ok = fd && write(fd.get(), &id, sizeof(id)) == static_cast<ssize_t>(sizeof(id)) &&
        (!sync || side_file_sync(fd.get())) && std::rename(tmp.c_str(), out.c_str()) == 0;
    if (!ok) {
        std::remove(tmp.c_str());
        throw exception((sstream() << "failed to write '" << out << "': " << strerror(errno)).str());
    }
}

// Reads the header of the pack `fname` open as `fd`; whether it is whole and the file has the identity
// recorded after it was written (`pack_identity_ok`), as `.olean` files are used if they have the
// identity a pack records for them.
bool read_pack_header(std::string const & fname, int fd, struct stat & st, pack_header & hdr, std::string & err) {
    if (fd < 0) { err = strerror(errno); return false; }
    if (fstat(fd, &st) != 0) { err = strerror(errno); return false; }
    if (!S_ISREG(st.st_mode)) { err = "not a regular file"; return false; }
    if (static_cast<uint64_t>(st.st_size) < g_pack_header_space ||
        pread(fd, &hdr, sizeof(hdr), 0) != static_cast<ssize_t>(sizeof(hdr))) {
        err = "not a PaperLean side file"; return false;
    }
    if (char const * why = check_side_file_header(hdr.common, g_pack_kind, sizeof(pack_header))) {
        err = why; return false;
    }
    if (hdr.olean_flags != olean_header_flags()) { err = "written by a different build of Lean"; return false; }
    if (hdr.format != g_pack_format) { err = "written by a different version"; return false; }
    if (hdr.size != static_cast<uint64_t>(st.st_size)) { err = "its size differs from the recorded one"; return false; }
    if (pack_header_checksum(hdr) != hdr.header_checksum) { err = "corrupt (checksum mismatch)"; return false; }
    if (!pack_identity_ok(fname, hdr.common.checksum, st)) { err = "it changed since it was written"; return false; }
    if (hdr.validated != g_pack_validated) { err = "corrupt"; return false; }
    return true;
}

/*
Checks the header of a pack and maps it. Like `.olean` files, packs are written to a temporary file
that is then renamed.
*/
bool load_pack_core(std::string const & fname, loaded_pack & p, std::string & err) {
    p.fname = fname;
    file_descriptor fd(open(fname.c_str(), O_RDONLY | O_CLOEXEC | O_NONBLOCK));
    struct stat st;
    pack_header hdr;
    if (!read_pack_header(fname, fd.get(), st, hdr, err)) return false;
    if (!p.init_header(hdr)) { err = "corrupt"; return false; }
    void * addr = reinterpret_cast<void *>(p.hdr.base_addr);
    // (not reserved: the pack is backed by its file, and larger than the memory of small machines)
    int flags = MAP_PRIVATE | MAP_NORESERVE
#ifdef MAP_FIXED_NOREPLACE
        | MAP_FIXED_NOREPLACE
#endif
        ;
    // Writable like the mappings of single files: the parts of a chain read from disk fix their
    // own pointers, never the pack's, but this keeps the two kinds of regions interchangeable.
    void * m = mmap(addr, p.hdr.size, PROT_READ | PROT_WRITE, flags, fd.get(), 0);
    if (m == MAP_FAILED || m != addr) {
        int error = errno;
        if (m != MAP_FAILED) munmap(m, p.hdr.size);
        err = std::string("its address range is not available") + (m == MAP_FAILED ? std::string(": ") + strerror(error) : std::string());
        return false;
    }
    p.begin = static_cast<char *>(m);
    char const * sums = p.begin + p.hdr.block_sums_off;
    if (side_file_checksum4(sums, p.hdr.size - p.hdr.block_sums_off, g_block_sums_seed) != p.hdr.block_sums_checksum) {
        err = "corrupt (checksum mismatch)"; return false;
    }
    p.block_table.reset(new side_file_blocks());
    p.block_table->init(p.begin + p.hdr.entries_off, p.hdr.block_sums_off - p.hdr.entries_off,
                        reinterpret_cast<uint64_t const *>(sums));
    p.blocks = p.block_table.get();
    p.set_tables(p.begin + p.hdr.entries_off);
    for (uint64_t i = 0; i < p.hdr.num_roots; i++) {
        if (!p.used(p.root_strings[i]) || !p.valid_str(p.root_strings[i])) { err = "corrupt"; return false; }
        p.roots.emplace_back(resolve_root(fname, std::string(p.str(p.root_strings[i]))));
    }
    err.clear();
    p.root_fds.reset(new std::atomic<int>[p.roots.size()]);
    for (size_t r = 0; r < p.roots.size(); r++) {
        int error = 0;
        int rfd = root_dir_fd(p.roots[r], error);
        // Files below a root that cannot be opened are read from disk.
        if (rfd < 0 && err.empty())
            err = error == EMFILE || error == ENFILE
                ? "too many open files to open root '" + p.roots[r] + "', so its files are read from disk"
                : "root '" + p.roots[r] + "' is not a directory, so its files are read from disk";
        p.root_fds[r].store(rfd, std::memory_order_relaxed);
    }
    auto states = [](uint64_t n) { return std::unique_ptr<std::atomic<uint8_t>[]>(new std::atomic<uint8_t>[n]()); };
    p.chain_state.reset(new std::atomic<uint32_t>[p.hdr.num_chains]());
    p.module_state = states(p.hdr.num_modules);
    p.part_state = states(p.hdr.num_entries);
    p.names_state = states(p.hdr.num_entries);
    p.warned.reset(new std::atomic<bool>(false));
    return true;
}

// Like `load_pack_core`, releasing everything on failure. On success, `err` may hold a warning.
bool load_pack(std::string const & fname, loaded_pack & p, std::string & err) {
    bool ok = false;
    try {
        ok = load_pack_core(fname, p, err);
    } catch (std::exception & ex) {
        err = ex.what();
    } catch (...) {
        err = "unexpected error";
    }
    if (!ok) {
        if (p.begin) munmap(p.begin, p.hdr.size);
        p.begin = nullptr;
        p.root_fds.reset();
    }
    return ok;
}
#endif

void init_packs() {
    auto * packs = new std::vector<loaded_pack>();
#if defined(LEAN_MMAP) && !defined(LEAN_WINDOWS)
    if (char const * env = getenv("LEAN_OLEAN_PACK")) {
        std::string list(env);
        size_t start = 0;
        while (start <= list.size()) {
            size_t end = list.find(':', start);
            if (end == std::string::npos) end = list.size();
            std::string fname = list.substr(start, end - start);
            start = end + 1;
            if (fname.empty()) continue;
            loaded_pack p;
            std::string err;
            if (load_pack(fname, p, err)) {
                if (!err.empty()) side_file_warning("warning: olean pack '%s': %s\n", fname.c_str(), err.c_str());
                packs->push_back(std::move(p));
            } else {
                side_file_warning("warning: ignoring olean pack '%s': %s\n", fname.c_str(), err.c_str());
            }
        }
    }
#endif
    g_packs.store(packs, std::memory_order_release);
}

// The `module_*` bits of module `i` of pack `pi`, found the first time.
uint8_t module_status(std::vector<loaded_pack> & packs, size_t pi, uint32_t i) {
    loaded_pack & p = packs[pi];
    uint8_t s = p.module_state[i].load(std::memory_order_acquire);
    if (s != 0) return s;
    s = module_known;
    if (!p.module_ok(i)) {
        p.damaged();
    } else {
        s |= module_valid;
        pack_module const & m = p.modules[i];
        // as `find_in_packs` picks the pack of the module's `.olean`
        std::string olean = p.roots[m.root_idx] + "/" + std::string(p.str(m.stem)) + ".olean";
        bool decided = false;
        for (size_t pj = 0; pj <= pi && !decided; pj++) {
            loaded_pack & q = packs[pj];
            for (size_t r = 0; r < q.roots.size(); r++) {
                std::string const & root = q.roots[r];
                if (olean.size() > root.size() + 1 && olean.compare(0, root.size(), root) == 0 && olean[root.size()] == '/') {
                    int64_t e = q.find_path(static_cast<uint32_t>(r), std::string_view(olean).substr(root.size() + 1));
                    if (e == -2) q.damaged();
                    if (e >= 0) {
                        decided = true;
                        if (pj == pi && r == m.root_idx) s |= module_here;
                    }
                    break;
                }
            }
        }
    }
    p.module_state[i].store(s, std::memory_order_release);
    return s;
}

// Whether no file of `chain` changed since packing and its entries are consistent: 1 if so, 2
// otherwise.
uint8_t check_chain_files(loaded_pack & p, uint32_t chain) {
#if defined(LEAN_MMAP) && !defined(LEAN_WINDOWS)
    if (!p.chain_ok(chain)) {
        p.damaged();
        return 2;
    }
    bool githash_checked = olean_githash_checked();
    pack_chain const & c = p.chains[chain];
    for (uint32_t i = c.first; i < c.first + c.count; i++) {
        pack_entry const & ce = p.entries[i];
        // a file that Lean would not load is read from the disk, which reports it as Lean does
        if (githash_checked && !(ce.flags & entry_githash_match))
            return 2;
        char rel[PATH_MAX];
        struct stat st;
        int root_fd = p.root_fds[ce.root_idx].load(std::memory_order_relaxed);
        if (ce.path.len >= sizeof(rel) || root_fd < 0)
            return 2;
        memcpy(rel, p.strings + ce.path.off, ce.path.len);
        rel[ce.path.len] = 0;
        if (fstatat(root_fd, rel, &st, 0) != 0 || !same_file_id(ce, st))
            return 2;
    }
    return 1;
#else
    // packs are not loaded on this platform
    (void)p; (void)chain;
    return 2;
#endif
}

// The state of `chain` for the current generation of imports.
uint8_t chain_state_now(loaded_pack const & p, uint32_t chain) {
    uint32_t v = p.chain_state[chain].load(std::memory_order_acquire);
    return (v >> 2) == g_pack_generation.load(std::memory_order_acquire) ? v & 3 : 0;
}

// Checks `chain` for the current generation unless it is checked already or being checked; returns
// false in the latter case.
bool try_check_chain(loaded_pack & p, uint32_t chain) {
    uint32_t generation = g_pack_generation.load(std::memory_order_acquire);
    uint32_t seen = p.chain_state[chain].load(std::memory_order_acquire);
    if ((seen >> 2) == generation && (seen & 3) != 0) return (seen & 3) != 3;
    uint32_t checking = generation << 2 | 3;
    if (!p.chain_state[chain].compare_exchange_strong(seen, checking, std::memory_order_acq_rel))
        return false;
    uint8_t state = check_chain_files(p, chain);
    // (unless a thread of a later generation took over)
    p.chain_state[chain].compare_exchange_strong(checking, generation << 2 | state, std::memory_order_acq_rel);
    if (state == 2) g_changed_chains.fetch_add(1, std::memory_order_acq_rel);
    return true;
}

// Whether no file of `chain` changed since packing (checked once per chain and generation).
bool chain_unchanged(loaded_pack & p, uint32_t chain) {
    uint8_t state = chain_state_now(p, chain);
    if (state == 0 || state == 3) {
        scoped_import_timer validate_timer(counter_pack_validate);
        do {
            // a validator may be checking it
            while (!try_check_chain(p, chain))
                std::this_thread::yield();
            state = chain_state_now(p, chain);
        } while (state == 0 || state == 3);
    }
    return state == 1;
}

// Threads that check the chains that fast imports serve before checking them (`serve_chain`). Two
// mostly keep up with an import; more contend for the file system and cost CPU time.
constexpr unsigned g_validator_threads = 2;
struct validator {
    std::mutex m_mutex;
    std::condition_variable m_cv;
    std::deque<std::pair<loaded_pack *, uint32_t>> m_queue;
    bool m_started = false;
    unsigned m_threads = 0;

    void run() {
        while (true) {
            std::pair<loaded_pack *, uint32_t> item;
            {
                std::unique_lock<std::mutex> lock(m_mutex);
                m_cv.wait(lock, [&] { return !m_queue.empty(); });
                item = m_queue.front();
                m_queue.pop_front();
            }
            try_check_chain(*item.first, item.second);
        }
    }
    template<class It> void add(It begin, It end) {
        std::unique_lock<std::mutex> lock(m_mutex);
        if (!m_started) {
            m_started = true;
            try {
                for (; m_threads < g_validator_threads; m_threads++)
                    std::thread([this] { run(); }).detach();
            } catch (std::system_error &) {}
        }
        // without threads, the chains are checked when the import ends
        if (m_threads == 0) return;
        m_queue.insert(m_queue.end(), begin, end);
        m_cv.notify_all();
    }
};

validator * g_validator = new validator();

// The chains that the fast import of a thread served before they were checked, the number of them
// given to the validators, and `g_changed_chains` when they were last looked at. While it runs
// (`importing`), the files it serves and reads from disk are counted here, and added to
// `g_pack_served` and `g_pack_not_served` if it succeeds: `importModulesCore` reads them again if not.
struct unchecked_chains {
    std::vector<std::pair<loaded_pack *, uint32_t>> chains;
    size_t queued = 0;
    size_t changed_seen = 0;
    bool importing = false;
    size_t served = 0, not_served = 0;
};
thread_local unchecked_chains * t_unchecked = nullptr;

void count_served(bool served) {
    unchecked_chains * u = t_unchecked;
    if (u && u->importing) (served ? u->served : u->not_served)++;
    else (served ? g_pack_served : g_pack_not_served)++;
}
// A fast import gives the chains it serves unchecked to the validators in batches of this size.
constexpr size_t g_validation_batch = 16;

// For a fast import: whether `chain` can be served. If it is not checked yet, it is served now and
// checked before the import ends (`lean_paperlean_pack_join`), which is repeated as
// `importModulesCore` if a file changed.
bool serve_chain(loaded_pack & p, uint32_t chain) {
    uint8_t state = chain_state_now(p, chain);
    if (state == 1) return true;
    if (state == 2) return false;
    if (!t_unchecked) t_unchecked = new unchecked_chains();
    unchecked_chains & u = *t_unchecked;
    // a changed chain that the import served ends it early
    size_t changed = g_changed_chains.load(std::memory_order_acquire);
    if (changed != u.changed_seen) {
        u.changed_seen = changed;
        for (auto const & c : u.chains)
            if (chain_state_now(*c.first, c.second) == 2) return false;
    }
    u.chains.push_back({ &p, chain });
    if (u.chains.size() - u.queued >= g_validation_batch) {
        g_validator->add(u.chains.begin() + u.queued, u.chains.end());
        u.queued = u.chains.size();
    }
    return true;
}
}

bool find_in_packs(std::string const & fname, std::vector<region_view> const & deps, pack_hit & hit) {
    std::call_once(g_packs_once, init_packs);
    scoped_import_timer timer(counter_pack_lookup);
#if defined(LEAN_MMAP) && !defined(LEAN_WINDOWS)
    // The first pack that has the file below the first of its roots that is a prefix of its path
    // decides (`module_here` follows the same rule); a later pack can then add files below the same
    // root or replace files that changed (`paperlean build --prepare`).
    bool below_root = false;
    for (loaded_pack & p : *g_packs.load(std::memory_order_acquire)) {
        for (size_t r = 0; r < p.roots.size(); r++) {
            std::string const & root = p.roots[r];
            if (fname.size() <= root.size() + 1 || fname.compare(0, root.size(), root) != 0 ||
                fname[root.size()] != '/')
                continue;
            below_root = true;
            int64_t idx = p.find_path(static_cast<uint32_t>(r), std::string_view(fname).substr(root.size() + 1));
            if (idx == -2) p.damaged();
            if (idx < 0)
                break;
            pack_entry const & e = p.entries[idx];
            if (e.chain >= p.hdr.num_chains) p.damaged();
            bool deps_match = e.chain < p.hdr.num_chains && chain_unchanged(p, e.chain);
            // checking the chain checked its entries, among them `e` if it is part `e.part` of it
            if (deps_match && (e.part >= p.chains[e.chain].count ||
                               static_cast<uint64_t>(p.chains[e.chain].first) + e.part != static_cast<uint64_t>(idx))) {
                p.damaged();
                deps_match = false;
            }
            // The earlier parts of the chain must be exactly the given dependencies, as served from
            // this pack.
            deps_match = deps_match && deps.size() == e.part;
            for (uint32_t i = 0; deps_match && i < e.part; i++)
                deps_match = deps[i].begin == p.begin + p.entries[p.chains[e.chain].first + i].offset;
            if (!deps_match) {
                count_served(false);
                return false;
            }
            hit = { p.begin + e.offset, e.size, e.orig_base, reinterpret_cast<object *>(e.root),
                    reinterpret_cast<object *>(e.region_root) };
            count_served(true);
            return true;
        }
    }
    // (a file that does not exist, such as the `.ir.sig` of a file that is not a `module`, is not read)
    struct stat st;
    if (below_root && stat(fname.c_str(), &st) == 0) count_served(false);
#else
    (void)fname; (void)deps; (void)hit;
#endif
    return false;
}

bool in_packs(void const * addr) {
    std::vector<loaded_pack> * packs = g_packs.load(std::memory_order_acquire);
    if (!packs) return false;
    for (loaded_pack const & p : *packs)
        if (addr >= p.begin && addr < p.begin + p.hdr.size) return true;
    return false;
}

void extension_name_key(b_obj_arg n, std::string & key) { ext_name_key(n, key); }

void for_each_first_pack_ext_entries(b_obj_arg ext_name, std::function<void(object *)> const & f) {
    std::call_once(g_packs_once, init_packs);
    std::vector<loaded_pack> & packs = *g_packs.load(std::memory_order_acquire);
    if (packs.empty()) return;
    std::string key;
    ext_name_key(ext_name, key);
    loaded_pack & p = packs[0];
    std::vector<char> match(p.hdr.num_ext_names, 0);
    for (uint64_t i = 0; i < p.hdr.num_ext_names; i++) {
        std::string k;
        ext_name_key(reinterpret_cast<object *>(p.ext_names[i].name), k);
        match[i] = k == key;
    }
    for (uint64_t e = 0; e < p.hdr.num_ext_entries; e++)
        if (match[p.ext_entries[e].name]) f(reinterpret_cast<object *>(p.ext_entries[e].entries));
}

bool first_pack_identity(uint64_t & checksum, uint64_t & base, uint64_t & size) {
    std::call_once(g_packs_once, init_packs);
    std::vector<loaded_pack> & packs = *g_packs.load(std::memory_order_acquire);
    if (packs.empty()) return false;
    checksum = packs[0].hdr.common.checksum;
    base = packs[0].hdr.base_addr;
    size = packs[0].hdr.size;
    return true;
}

char const * first_pack_damaged() {
    std::call_once(g_packs_once, init_packs);
    std::vector<loaded_pack> & packs = *g_packs.load(std::memory_order_acquire);
    if (packs.empty()) return nullptr;
    static char const * why = packs[0].check_all();
    return why;
}

/* OLeanPack.stats : BaseIO (Nat × Nat) */
extern "C" LEAN_EXPORT obj_res lean_paperlean_olean_pack_stats() {
    object * r = alloc_cnstr(0, 2, 0);
    cnstr_set(r, 0, lean_usize_to_nat(g_pack_served.load()));
    cnstr_set(r, 1, lean_usize_to_nat(g_pack_not_served.load()));
    return r;
}

/*
OLeanPack.writeCore (chains : @& Array (Array String)) (roots storedRoots : @& Array String) (out : @& String)
  (baseAddr : USize) (sync : Bool) : IO Nat

Each chain lists the parts of one module in loading order; every file must lie below one of
`roots`, which the pack records as `storedRoots` (see `resolve_root`). Chains with a file that cannot
be packed (unreadable, or containing closures, whose function pointers are relocated per process)
are left out. With `sync`, the pack is on the disk before it gets its name. Returns the number of
packed files.
*/
extern "C" LEAN_EXPORT obj_res lean_paperlean_olean_pack_write(b_obj_arg ochains, b_obj_arg oroots, b_obj_arg ostored,
                                                     b_obj_arg oout, size_t base, uint8_t sync) {
#if defined(LEAN_MMAP) && !defined(LEAN_WINDOWS)
    std::string out(lean_string_cstr(oout));
    std::string tmp = out + ".tmp." + std::to_string(getpid());
    char * mem = nullptr;
    size_t total = 0;
    try {
        std::vector<std::string> roots;
        for (size_t i = 0; i < lean_array_size(oroots); i++)
            roots.emplace_back(lean_string_cstr(lean_array_get_core(oroots, i)));
        struct part {
            std::string path;
            uint32_t root_idx;
            struct stat st;
            size_t orig_base;
            uint8_t version;
            size_t data_off, data_size, offset;
        };
        std::vector<std::vector<part>> chains;
        size_t offset = g_pack_header_space;
        // A file listed twice (e.g. below nested roots) is packed once, with its first chain.
        std::unordered_set<std::string> packed_paths;
        for (size_t i = 0; i < lean_array_size(ochains); i++) {
            b_obj_arg ochain = lean_array_get_core(ochains, i);
            std::vector<part> chain;
            bool ok = lean_array_size(ochain) > 0;
            for (size_t j = 0; ok && j < lean_array_size(ochain); j++)
                ok = !packed_paths.count(lean_string_cstr(lean_array_get_core(ochain, j)));
            size_t chain_offset = offset;
            for (size_t j = 0; ok && j < lean_array_size(ochain); j++) {
                part pt;
                pt.path = lean_string_cstr(lean_array_get_core(ochain, j));
                ok = false;
                for (size_t r = 0; r < roots.size() && !ok; r++) {
                    std::string const & root = roots[r];
                    if (pt.path.size() > root.size() + 1 && pt.path.compare(0, root.size(), root) == 0 &&
                        pt.path[root.size()] == '/') {
                        pt.root_idx = static_cast<uint32_t>(r);
                        ok = true;
                    }
                }
                if (!ok) break;
                file_descriptor fd(open(pt.path.c_str(), O_RDONLY | O_CLOEXEC));
                std::vector<char> hdr(olean_header_size());
                ok = fd && fstat(fd.get(), &pt.st) == 0 && static_cast<size_t>(pt.st.st_size) >= hdr.size() + sizeof(size_t) &&
                    pread(fd.get(), hdr.data(), hdr.size(), 0) == static_cast<ssize_t>(hdr.size()) &&
                    olean_header_info(hdr.data(), pt.version, pt.orig_base) && (pt.version == 2 || pt.version == 3);
                if (!ok) break;
                size_t size = pt.st.st_size;
                pt.data_off = olean_header_size();
                pt.data_size = size - olean_header_size();
                if (pt.version == 3) {
                    uint64_t data_size; uint32_t num_closures = 0;
                    ok = pread(fd.get(), &data_size, sizeof(data_size), olean_header_size()) == sizeof(data_size) &&
                        data_size + olean_header_size() + sizeof(size_t) + sizeof(num_closures) <= size &&
                        pread(fd.get(), &num_closures, sizeof(num_closures),
                              olean_header_size() + sizeof(size_t) + data_size) == sizeof(num_closures) &&
                        num_closures == 0;
                    pt.data_off = olean_header_size() + sizeof(size_t);
                    pt.data_size = data_size;
                }
                pt.offset = offset;
                offset = align_up(offset + size, 64);
                chain.push_back(std::move(pt));
            }
            if (ok) {
                for (part const & pt : chain) packed_paths.insert(pt.path);
                chains.push_back(std::move(chain));
            } else {
                offset = chain_offset;
            }
        }
        total = offset;

        // Relocate every region to its address in the pack by loading it there.
        int flags = MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE
#ifdef MAP_FIXED_NOREPLACE
            | MAP_FIXED_NOREPLACE
#endif
            ;
        void * m = mmap(reinterpret_cast<void *>(base), total, PROT_READ | PROT_WRITE, flags, -1, 0);
        if (m == MAP_FAILED || m != reinterpret_cast<void *>(base)) {
            if (m != MAP_FAILED) munmap(m, total);
            throw exception((sstream() << "address range at " << reinterpret_cast<void *>(base) << " is not available").str());
        }
        mem = static_cast<char *>(m);
        file_descriptor ofd(open(tmp.c_str(), O_RDWR | O_CREAT | O_TRUNC | O_CLOEXEC, 0644));
        if (!ofd) throw exception((sstream() << "failed to create '" << tmp << "': " << strerror(errno)).str());
        auto write_at = [&](void const * data, size_t len, size_t off) {
            char const * p = static_cast<char const *>(data);
            while (len > 0) {
                ssize_t w = pwrite(ofd.get(), p, len, off);
                if (w < 0) {
                    if (errno == EINTR) continue;
                    throw exception((sstream() << "failed to write '" << tmp << "': " << strerror(errno)).str());
                }
                p += w; len -= w; off += w;
            }
        };
        std::vector<pack_entry> entries;
        std::vector<pack_chain> chain_table;
        // Root objects are copied into one area after the regions, so that an import touches a few
        // pages for all of them instead of a page per part. A root stays in place if a later part
        // of its chain may point to it (some word of the later part's data equals its address).
        uint64_t roots_area_off = align_up(total, 64);
        std::string roots_area;
        // Per part: the hashes of `constNames` and `extraConstNames`, and its chain.
        std::vector<std::vector<uint64_t>> part_hashes;
        std::vector<uint32_t> part_chain;
        // Per part, its `ModuleData` fields; extension names are numbered by their first occurrence.
        std::vector<pack_part> part_table;
        std::vector<pack_ext_entry> ext_entry_table;
        std::vector<pack_ext_name> ext_name_table;
        std::unordered_map<std::string, uint32_t> ext_name_index;
        auto describe_part = [&](object * data) {
            pack_part pp = {};
            object * arrays[4];
            for (unsigned i = 0; i < 4; i++) arrays[i] = module_data_field(data, 1 + i);
            pp.const_names = reinterpret_cast<uint64_t>(arrays[0]);
            pp.constants = reinterpret_cast<uint64_t>(arrays[1]);
            pp.extra_const_names = reinterpret_cast<uint64_t>(arrays[2]);
            pp.entries = reinterpret_cast<uint64_t>(arrays[3]);
            pp.num_const_names = static_cast<uint32_t>(lean_array_size(arrays[0]));
            pp.num_constants = static_cast<uint32_t>(lean_array_size(arrays[1]));
            pp.num_extra_const_names = static_cast<uint32_t>(lean_array_size(arrays[2]));
            pp.num_entries = static_cast<uint32_t>(lean_array_size(arrays[3]));
            pp.is_module = module_data_is_module(data);
            pp.first_ext = static_cast<uint32_t>(ext_entry_table.size());
            for (size_t i = 0; i < pp.num_entries; i++) {
                object * pair = lean_array_get_core(arrays[3], i);
                object * n = lean_ctor_get(pair, 0);
                std::string key;
                ext_name_key(n, key);
                auto it = ext_name_index.find(key);
                if (it == ext_name_index.end()) {
                    it = ext_name_index.emplace(key, static_cast<uint32_t>(ext_name_table.size())).first;
                    ext_name_table.push_back({ reinterpret_cast<uint64_t>(n) });
                }
                ext_entry_table.push_back({ reinterpret_cast<uint64_t>(lean_ctor_get(pair, 1)), it->second, 0 });
            }
            return pp;
        };
        // Modules by root and stem, filled while their regions are in memory; edge targets are
        // resolved by stem afterwards.
        struct writer_module {
            pack_module m = {};
            std::string stem;
            std::vector<pack_edge> edges;
            std::vector<std::string> edge_stems;   // empty if the name has no stem
        };
        std::vector<writer_module> modules;
        std::unordered_map<std::string, uint32_t> module_index;
        auto module_for = [&](uint32_t root_idx, std::string const & stem) -> writer_module & {
            std::string key = std::to_string(root_idx) + ":" + stem;
            auto it = module_index.find(key);
            if (it != module_index.end()) return modules[it->second];
            module_index.emplace(key, static_cast<uint32_t>(modules.size()));
            modules.emplace_back();
            writer_module & wm = modules.back();
            wm.stem = stem;
            wm.m.root_idx = root_idx;
            wm.m.olean_chain = wm.m.ir_chain = -1;
            return wm;
        };
        std::string strings;
        auto add_string = [&](std::string const & s) {
            pack_string r { strings.size(), s.size() };
            strings += s;
            return r;
        };
        for (auto & chain : chains) {
            // A chain with a file that changed since it was looked at is left out, like one with a
            // file that cannot be read: (the pack records the identity of the file as first opened)
            std::vector<std::unique_ptr<file_descriptor>> fds;
            bool unchanged = true;
            for (part const & pt : chain) {
                fds.emplace_back(new file_descriptor(open(pt.path.c_str(), O_RDONLY | O_CLOEXEC)));
                struct stat st;
                unchanged = unchanged && *fds.back() && fstat(fds.back()->get(), &st) == 0 && same_stat(pt.st, st);
            }
            if (!unchanged) continue;
            std::vector<region_view> deps;
            pack_chain c { static_cast<uint32_t>(entries.size()), static_cast<uint32_t>(chain.size()) };
            std::vector<object *> chain_roots;
            std::vector<bool> referenced;
            for (size_t j = 0; j < chain.size(); j++) {
                part & pt = chain[j];
                char * slot = mem + pt.offset;
                size_t size = pt.st.st_size;
                if (pread(fds[j]->get(), slot, size, 0) != static_cast<ssize_t>(size))
                    throw exception((sstream() << "failed to read '" << pt.path << "'").str());
                region_reader reader(pt.data_size, slot + pt.data_off,
                                     reinterpret_cast<char *>(pt.orig_base) + pt.data_off,
                                     deps, {}, {});
                object * root = reader.read();
                // the layout of `ModuleData` that the tables assume
                if (lean_is_scalar(root) || lean_ptr_tag(root) != 0 || lean_ctor_num_objs(root) != g_module_data_num_objs)
                    throw exception((sstream() << "'" << pt.path << "' does not hold module data").str());
                memcpy(slot + pt.data_off, &root, sizeof(root));
                size_t new_base = reinterpret_cast<size_t>(slot);
                memcpy(slot + olean_header_base_addr_offset(), &new_base, sizeof(new_base));
                write_at(slot, size, pt.offset);
                part_table.push_back(describe_part(root));
                std::vector<uint64_t> hashes;
                for (unsigned a = 1; a <= 3; a += 2) {
                    object * names = module_data_field(root, a);
                    for (size_t k = 0; k < lean_array_size(names); k++)
                        hashes.push_back(lean_name_hash(lean_array_get_core(names, k)));
                }
                part_hashes.push_back(std::move(hashes));
                part_chain.push_back(static_cast<uint32_t>(chain_table.size()));
                // the root slot of the data holds this part's root, which may be an earlier one's
                char const * words = slot + pt.data_off + sizeof(void *);
                size_t num_words = (pt.data_size - sizeof(void *)) / sizeof(void *);
                for (size_t r = 0; r < chain_roots.size(); r++) {
                    for (size_t w = 0; w < num_words && !referenced[r]; w++) {
                        uint64_t v;
                        memcpy(&v, words + w * sizeof(void *), sizeof(v));
                        if (v == reinterpret_cast<uint64_t>(chain_roots[r])) referenced[r] = true;
                    }
                }
                chain_roots.push_back(root);
                referenced.push_back(false);
                pack_entry e = {};
                e.offset = pt.offset;
                e.orig_base = pt.orig_base;
                e.root = e.region_root = reinterpret_cast<uint64_t>(root);
                set_file_id(e, pt.st);
                e.path = add_string(pt.path.substr(roots[pt.root_idx].size() + 1));
                e.root_idx = pt.root_idx;
                e.chain = static_cast<uint32_t>(chain_table.size());
                e.part = static_cast<uint32_t>(j);
                if (olean_header_githash_matches(slot)) e.flags |= entry_githash_match;
                entries.push_back(e);
                deps.push_back({ slot, size, reinterpret_cast<void *>(pt.orig_base) });
            }
            chain_table.push_back(c);
            // Copy the roots no later part points to; a root shared by several parts is copied once.
            for (size_t j = 0; j < chain.size(); j++) {
                object * root = chain_roots[j];
                size_t first = std::find(chain_roots.begin(), chain_roots.end(), root) - chain_roots.begin();
                if (first < j) {
                    entries[c.first + j].root = entries[c.first + first].root;
                } else if (!referenced[j] && lean_object_byte_size(root) == g_module_data_size) {
                    entries[c.first + j].root = base + roots_area_off + roots_area.size();
                    roots_area.append(reinterpret_cast<char const *>(root), g_module_data_size);
                }
            }
            std::string rel = chain.front().path.substr(roots[chain.front().root_idx].size() + 1), stem;
            if (ends_with(rel, ".olean", stem)) {
                writer_module & wm = module_for(chain.front().root_idx, stem);
                wm.m.olean_chain = static_cast<int32_t>(chain_table.size() - 1);
                object * data = chain_roots[0];
                if (module_data_is_module(data)) wm.m.flags |= pack_module_is_module;
                object * imports = module_data_imports(data);
                bool shared = true;
                for (object * r : chain_roots)
                    shared = shared && module_data_imports(r) == imports;
                if (shared) {
                    wm.m.flags |= pack_module_edges;
                    for (size_t j = 0; j < lean_array_size(imports); j++) {
                        object * imp = lean_array_get_core(imports, j);
                        pack_edge e = {};
                        e.module = reinterpret_cast<uint64_t>(lean_ctor_get(imp, 0));
                        e.target = -1;
                        e.import_all = import_flag(imp, 0);
                        e.is_exported = import_flag(imp, 1);
                        e.is_meta = import_flag(imp, 2);
                        std::string target;
                        if (!module_stem(lean_ctor_get(imp, 0), target)) target.clear();
                        wm.edges.push_back(e);
                        wm.edge_stems.push_back(target);
                    }
                }
            } else if (ends_with(rel, ".ir.sig", stem)) {
                module_for(chain.front().root_idx, stem).m.ir_chain = static_cast<int32_t>(chain_table.size() - 1);
            }
            // The chain is in the file now; release its memory, except for the last page, which the
            // next chain may share.
            size_t page = sysconf(_SC_PAGESIZE);
            size_t from = chain.front().offset & ~(page - 1);
            size_t to = (chain.back().offset + chain.back().st.st_size) & ~(page - 1);
#ifdef __APPLE__
            // (where `MADV_DONTNEED` releases nothing) new pages in place, in the writer's own range
            if (to > from)
                mmap(mem + from, to - from, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);
#else
            if (to > from) madvise(mem + from, to - from, MADV_DONTNEED);
#endif
        }
        std::vector<pack_string> root_table;
        for (size_t r = 0; r < roots.size(); r++)
            root_table.push_back(add_string(r < lean_array_size(ostored) ?
                std::string(lean_string_cstr(lean_array_get_core(ostored, r))) : roots[r]));
        // A stem found below several roots is ambiguous: which one the search path picks is only
        // known at run time.
        std::unordered_map<std::string, int64_t> module_of_stem;
        for (size_t i = 0; i < modules.size(); i++) {
            auto r = module_of_stem.emplace(modules[i].stem, static_cast<int64_t>(i));
            if (!r.second) r.first->second = -1;
        }
        std::vector<pack_module> module_table;
        std::vector<pack_edge> edge_table;
        for (writer_module & wm : modules) {
            name n;
            size_t start = 0;
            while (start <= wm.stem.size()) {
                size_t end = wm.stem.find('/', start);
                if (end == std::string::npos) end = wm.stem.size();
                n = name(n, wm.stem.substr(start, end - start).c_str());
                start = end + 1;
            }
            wm.m.name_hash = n.hash();
            wm.m.stem = add_string(wm.stem);
            wm.m.first_edge = static_cast<uint32_t>(edge_table.size());
            wm.m.num_edges = static_cast<uint32_t>(wm.edges.size());
            for (size_t j = 0; j < wm.edges.size(); j++) {
                auto it = wm.edge_stems[j].empty() ? module_of_stem.end() : module_of_stem.find(wm.edge_stems[j]);
                if (it != module_of_stem.end() && it->second >= 0) wm.edges[j].target = static_cast<int32_t>(it->second);
                edge_table.push_back(wm.edges[j]);
            }
            module_table.push_back(wm.m);
        }

        // The single-occurrence bits of the name tables. A module is identified by its `.olean` or
        // `.ir.sig` chain's module; other chains count as modules of their own.
        std::vector<uint32_t> chain_module(chain_table.size());
        for (size_t i = 0; i < chain_table.size(); i++) chain_module[i] = UINT32_MAX - static_cast<uint32_t>(i);
        for (size_t i = 0; i < modules.size(); i++) {
            if (modules[i].m.olean_chain >= 0) chain_module[modules[i].m.olean_chain] = static_cast<uint32_t>(i);
            if (modules[i].m.ir_chain >= 0) chain_module[modules[i].m.ir_chain] = static_cast<uint32_t>(i);
        }
        struct occurrence { uint32_t module; uint8_t array; bool single; };
        std::unordered_map<uint64_t, occurrence> occurrences;
        for (size_t i = 0; i < part_table.size(); i++) {
            std::vector<uint64_t> const & hs = part_hashes[i];
            uint32_t mod = chain_module[part_chain[i]];
            for (uint8_t a = 0; a < 2; a++) {
                size_t from = a == 0 ? 0 : part_table[i].num_const_names;
                size_t to = a == 0 ? part_table[i].num_const_names : hs.size();
                std::vector<uint64_t> sorted(hs.begin() + from, hs.begin() + to);
                std::sort(sorted.begin(), sorted.end());
                for (size_t k = 0; k < sorted.size(); k++) {
                    auto r = occurrences.emplace(sorted[k], occurrence { mod, a, true });
                    if (!r.second && (r.first->second.module != mod || r.first->second.array != a))
                        r.first->second.single = false;
                    if (k > 0 && sorted[k] == sorted[k - 1]) r.first->second.single = false;
                }
            }
        }
        uint64_t names_off = align_up(roots_area_off + roots_area.size(), 64);
        std::string names;
        for (size_t i = 0; i < part_table.size(); i++) {
            std::vector<uint64_t> const & hs = part_hashes[i];
            std::vector<uint64_t> table(hs);
            table.resize(hs.size() + (hs.size() + 63) / 64, 0);
            for (size_t k = 0; k < hs.size(); k++)
                if (occurrences[hs[k]].single) table[hs.size() + k / 64] |= uint64_t(1) << (k % 64);
            pack_part & pp = part_table[i];
            pp.names = names_off + names.size();
            pp.names_checksum = side_file_checksum(table.data(), table.size() * sizeof(uint64_t));
            names.append(reinterpret_cast<char const *>(table.data()), table.size() * sizeof(uint64_t));
        }

        pack_header hdr = {};
        init_side_file_header(hdr.common, g_pack_kind, sizeof(pack_header));
        hdr.olean_flags = olean_header_flags();
        hdr.format = g_pack_format;
        hdr.base_addr = base;
        hdr.roots_area_off = roots_area_off;
        hdr.names_off = names_off;
        uint64_t index_off = align_up(names_off + names.size(), 64);
        std::string index;
        auto append = [&](void const * data, size_t len) {
            size_t off = index_off + index.size();
            index.append(static_cast<char const *>(data), len);
            return off;
        };
        hdr.entries_off = append(entries.data(), entries.size() * sizeof(pack_entry));
        hdr.num_entries = entries.size();
        hdr.chains_off = append(chain_table.data(), chain_table.size() * sizeof(pack_chain));
        hdr.num_chains = chain_table.size();
        hdr.roots_off = append(root_table.data(), root_table.size() * sizeof(pack_string));
        hdr.num_roots = root_table.size();
        uint64_t hash_size = 1;
        while (hash_size < 2 * entries.size()) hash_size *= 2;
        std::vector<std::pair<uint64_t, uint64_t>> roots_hash(hash_size, {0, 0});
        for (size_t i = 0; i < entries.size(); i++) {
            uint64_t slot = root_slot(entries[i].root, hash_size);
            while (roots_hash[slot].first != 0 && roots_hash[slot].first != entries[i].root) slot = (slot + 1) & (hash_size - 1);
            // a root shared by several parts maps to the first; they have the same fields
            if (roots_hash[slot].first == 0) roots_hash[slot] = { entries[i].root, i };
        }
        hdr.roots_hash_off = append(roots_hash.data(), roots_hash.size() * sizeof(roots_hash[0]));
        hdr.roots_hash_size = hash_size;
        hdr.parts_off = append(part_table.data(), part_table.size() * sizeof(pack_part));
        hdr.ext_entries_off = append(ext_entry_table.data(), ext_entry_table.size() * sizeof(pack_ext_entry));
        hdr.num_ext_entries = ext_entry_table.size();
        hdr.ext_names_off = append(ext_name_table.data(), ext_name_table.size() * sizeof(pack_ext_name));
        hdr.num_ext_names = ext_name_table.size();
        hdr.modules_off = append(module_table.data(), module_table.size() * sizeof(pack_module));
        hdr.num_modules = module_table.size();
        hdr.edges_off = append(edge_table.data(), edge_table.size() * sizeof(pack_edge));
        hdr.num_edges = edge_table.size();
        uint64_t paths_size = 1;
        while (paths_size < 2 * entries.size()) paths_size *= 2;
        std::vector<pack_path_slot> paths(paths_size, pack_path_slot { 0, 0 });
        for (size_t i = 0; i < entries.size(); i++) {
            uint64_t h = path_hash(entries[i].root_idx, std::string_view(strings.data() + entries[i].path.off, entries[i].path.len));
            uint64_t slot = h & (paths_size - 1);
            while (paths[slot].entry != 0) slot = (slot + 1) & (paths_size - 1);
            paths[slot] = { static_cast<uint32_t>(i + 1), static_cast<uint32_t>(h >> 32) };
        }
        hdr.paths_off = append(paths.data(), paths.size() * sizeof(pack_path_slot));
        hdr.paths_size = paths_size;
        std::vector<pack_module_hash> modules_by_hash;
        for (size_t i = 0; i < module_table.size(); i++)
            modules_by_hash.push_back({ module_table[i].name_hash, static_cast<uint32_t>(i), 0 });
        std::sort(modules_by_hash.begin(), modules_by_hash.end(), [](pack_module_hash const & a, pack_module_hash const & b) {
            return a.hash < b.hash || (a.hash == b.hash && a.module < b.module);
        });
        hdr.modules_by_hash_off = append(modules_by_hash.data(), modules_by_hash.size() * sizeof(pack_module_hash));
        hdr.strings_off = append(strings.data(), strings.size());
        hdr.strings_size = strings.size();
        while (index.size() % 8) index.push_back(0);
        hdr.block_sums_off = hdr.entries_off + index.size();
        std::string sums = side_file_block_sums(index.data(), index.size());
        hdr.block_sums_checksum = side_file_checksum4(sums.data(), sums.size(), g_block_sums_seed);
        index += sums;
        hdr.size = hdr.entries_off + index.size();
        // Readers check the bounds of the entries they use; the blocks' checksums keep them as checked here.
        {
            pack_tables t;
            if (!t.init_header(hdr))
                throw exception("its layout is inconsistent");
            t.set_tables(index.data());
            if (char const * why = t.check_all())
                throw exception((sstream() << "its index is inconsistent: " << why).str());
        }
        hdr.validated = g_pack_validated;
        write_at(roots_area.data(), roots_area.size(), roots_area_off);
        write_at(names.data(), names.size(), names_off);
        write_at(index.data(), index.size(), hdr.entries_off);
        if (ftruncate(ofd.get(), hdr.size) != 0)
            throw exception((sstream() << "failed to write '" << tmp << "': " << strerror(errno)).str());
        munmap(mem, total);
        mem = nullptr;
        // the checksum of the regions as written
        if (int e = pack_payload_checksum(ofd.get(), hdr.entries_off, hdr.payload_checksum))
            throw exception((sstream() << "failed to read '" << tmp << "': " << strerror(e)).str());
        hdr.header_checksum = pack_header_checksum(hdr);
        hdr.common.checksum = pack_checksum(hdr, index.data(), index.size());
        write_at(&hdr, sizeof(hdr), 0);
        // read-only: a tool writing to a mapped pack in place fails, instead of crashing processes
        // or changing their results
        if (fchmod(ofd.get(), 0444) != 0)
            throw exception((sstream() << "failed to make '" << tmp << "' read-only").str());
        // the pack is on the disk before its name is, so that one found under its name is whole
        if (sync && !side_file_sync(ofd.get()))
            throw exception((sstream() << "failed to write '" << tmp << "': " << strerror(errno)).str());
        // Locked until its identity is recorded, which can only come after the rename, as that changes
        // the file's status change time: a build that finds it under its name meanwhile waits at its
        // shared lock (`toolchainPack` in `Lake/PaperLean/BuildData.lean`), and does not remove it.
        flock(ofd.get(), LOCK_EX);
        if (std::rename(tmp.c_str(), out.c_str()) != 0)
            throw exception((sstream() << "failed to write '" << out << "': " << strerror(errno)).str());
        if (sync) {
            size_t slash = out.rfind('/');
            file_descriptor dfd(open(slash == std::string::npos ? "." : out.substr(0, slash + 1).c_str(), O_RDONLY | O_DIRECTORY | O_CLOEXEC));
            if (dfd) side_file_sync(dfd.get());
        }
        write_pack_identity(out, hdr.common.checksum, sync);
        return io_result_mk_ok(lean_usize_to_nat(entries.size()));
    } catch (std::exception & ex) {
        if (mem) munmap(mem, total);
        std::remove(tmp.c_str());
        return io_result_mk_error((sstream() << "failed to create olean pack '" << out << "': " << ex.what()).str());
    }
#else
    (void)ochains; (void)oroots; (void)base; (void)sync;
    return io_result_mk_error((sstream() << "failed to create olean pack '" << lean_string_cstr(oout)
                                         << "': not supported on this platform").str());
#endif
}

// =======================================
// Modules of olean packs, for `importModules`
//
// A module is identified by `pack index << 24 | module index`; `g_no_pack_module` means none.

namespace {
constexpr uint32_t g_no_pack_module = 0xffffffff;

loaded_pack * pack_of(uint32_t id, uint32_t & idx) {
    std::call_once(g_packs_once, init_packs);
    std::vector<loaded_pack> & packs = *g_packs.load(std::memory_order_acquire);
    uint32_t pi = id >> 24;
    idx = id & 0xffffff;
    if (id == g_no_pack_module || pi >= packs.size() || idx >= packs[pi].hdr.num_modules ||
        !(module_status(packs, pi, idx) & module_valid))
        return nullptr;
    return &packs[pi];
}

// The parts of `chain` as `(ModuleData × CompactedRegion)` pairs, served like `lean_compacted_region_read`.
obj_res pack_chain_parts(loaded_pack & p, uint32_t chain, size_t count) {
    pack_chain const & c = p.chains[chain];
    object * parts = lean_alloc_array(0, count);
    for (uint32_t i = c.first; i < c.first + count; i++) {
        pack_entry const & e = p.entries[i];
        std::string path = p.roots[e.root_idx] + "/" +
            std::string(p.begin + p.hdr.strings_off + e.path.off, e.path.len);
        object * opath = lean_mk_string_from_bytes(path.data(), path.size());
        object * root = reinterpret_cast<object *>(e.root);
        object * pair = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(pair, 0, root);
        lean_ctor_set(pair, 1, mk_olean_region(opath, reinterpret_cast<object *>(e.region_root), p.begin + e.offset,
                                               e.orig_base, e.size, true));
        lean_dec(opath);
        parts = lean_array_push(parts, pair);
        count_served(true);
    }
    return parts;
}

}

// The metadata of the packed part whose root `ModuleData` is `root`, if any.
pack_part const * packed_part(b_obj_arg root, loaded_pack ** pack = nullptr) {
    std::vector<loaded_pack> * packs = g_packs.load(std::memory_order_acquire);
    if (!packs || lean_is_scalar(root)) return nullptr;
    uint64_t a = reinterpret_cast<uint64_t>(root);
    for (loaded_pack & p : *packs) {
        if (a < p.hdr.base_addr || a >= p.hdr.base_addr + p.hdr.entries_off) continue;
        int64_t i = p.find_root(a);
        if (i == -2) p.damaged();
        if (i < 0) return nullptr;
        uint8_t state = p.part_state[i].load(std::memory_order_acquire);
        if (state == 0) {
            state = p.part_ok(static_cast<uint64_t>(i)) ? 1 : 2;
            if (state == 2) p.damaged();
            p.part_state[i].store(state, std::memory_order_release);
        }
        if (state != 1) return nullptr;
        if (pack) *pack = &p;
        return &p.parts[i];
    }
    return nullptr;
}

/* packModuleFind (name : @& Name) : UInt32
   The pack module named `name` whose `.olean` chain is packed together with its imports. */
extern "C" LEAN_EXPORT uint32_t lean_paperlean_pack_module_find(b_obj_arg n) {
    std::call_once(g_packs_once, init_packs);
    scoped_import_timer timer(counter_pack_find);
    std::vector<loaded_pack> & packs = *g_packs.load(std::memory_order_acquire);
    uint64_t h = lean_name_hash(n);
    std::string stem;
    bool have_stem = false;
    for (size_t pi = 0; pi < packs.size() && pi < 255; pi++) {
        loaded_pack & p = packs[pi];
        bool damaged = false;
        for (uint64_t k = p.first_module_with_hash(h, damaged); k < p.hdr.num_modules; k++) {
            if (!p.used(p.modules_by_hash[k])) { damaged = true; break; }
            if (p.modules_by_hash[k].hash != h) break;
            uint32_t i = p.modules_by_hash[k].module;
            if (i >= p.hdr.num_modules) { damaged = true; continue; }
            uint8_t s = module_status(packs, pi, i);
            if (!(s & module_valid) || !(s & module_here) || !(p.modules[i].flags & pack_module_edges)) continue;
            if (!have_stem) {
                if (!module_stem(n, stem)) return g_no_pack_module;
                have_stem = true;
            }
            if (p.str(p.modules[i].stem) == stem)
                return static_cast<uint32_t>(pi << 24) | i;
        }
        if (damaged) p.damaged();
    }
    return g_no_pack_module;
}

bool stat_identity(char const * path, file_identity & id) {
#if defined(LEAN_MMAP) && !defined(LEAN_WINDOWS)
    struct stat st;
    if (stat(path, &st) != 0) return false;
    pack_entry e;
    set_file_id(e, st);
    id = file_identity { e.dev, e.ino, e.size, e.mtime_sec, e.mtime_nsec, e.ctime_sec, e.ctime_nsec };
    return true;
#else
    (void)path; (void)id;
    return false;
#endif
}

uint32_t module_file_kind_of(std::string_view path) {
    auto ends = [&](std::string_view ext) {
        return path.size() > ext.size() && path.compare(path.size() - ext.size(), ext.size(), ext) == 0;
    };
    if (ends(".olean")) return file_olean;
    if (ends(".olean.server")) return file_olean_server;
    if (ends(".olean.private")) return file_olean_private;
    if (ends(".ir.sig")) return file_ir_sig;
    if (ends(".ir")) return file_ir;
    return num_module_file_kinds;
}

bool packed_module_files(b_obj_arg n, b_obj_arg data, std::vector<std::pair<uint32_t, file_identity>> & files) {
    files.clear();
    uint32_t m = lean_paperlean_pack_module_find(n);
    if (m == g_no_pack_module) return false;
    uint32_t idx;
    loaded_pack * p = pack_of(m, idx);
    loaded_pack * dp = nullptr;
    pack_part const * pp = p ? packed_part(data, &dp) : nullptr;
    if (!pp || dp != p) return false;
    pack_module const & pm = p->modules[idx];
    uint32_t chain = p->entries[pp - p->parts].chain;
    if (static_cast<int32_t>(chain) != pm.olean_chain && static_cast<int32_t>(chain) != pm.ir_chain) return false;
    if ((pm.flags & pack_module_is_module) && (pm.ir_chain < 0 || p->chains[pm.ir_chain].count != 2)) return false;
    for (int32_t c : { pm.olean_chain, pm.ir_chain }) {
        if (c < 0) continue;
        if (!chain_unchanged(*p, c)) return false;
        for (uint32_t i = p->chains[c].first; i < p->chains[c].first + p->chains[c].count; i++) {
            pack_entry const & e = p->entries[i];
            uint32_t kind = module_file_kind_of(std::string_view(p->begin + p->hdr.strings_off + e.path.off, e.path.len));
            if (kind == num_module_file_kinds) return false;
            files.push_back({ kind, file_identity { e.dev, e.ino, e.size, e.mtime_sec, e.mtime_nsec, e.ctime_sec, e.ctime_nsec } });
        }
    }
    std::sort(files.begin(), files.end(), [](auto const & a, auto const & b) { return a.first < b.first; });
    for (size_t i = 1; i < files.size(); i++)
        if (files[i].first == files[i - 1].first) return false;
    return true;
}

#if defined(LEAN_MMAP) && !defined(LEAN_WINDOWS)
namespace {
// A pack's index, read without mapping the pack, for `packStaleness` and `packFreshFiles`.
struct pack_index_file {
    std::string fname;
    pack_header hdr;
    std::vector<char> index;
    pack_entry const * entries = nullptr;
    pack_chain const * chains = nullptr;
    pack_string const * roots = nullptr;
    pack_module const * modules = nullptr;
    char const * strings = nullptr;
    std::vector<std::string> root_paths;  // resolved
    std::vector<int> root_fds;

    ~pack_index_file() { for (int rfd : root_fds) if (rfd >= 0) close(rfd); }
    bool str_ok(pack_string x) const { return x.off <= hdr.strings_size && x.len <= hdr.strings_size - x.off; }
    std::string str(pack_string x) const { return std::string(strings + x.off, x.len); }

    // Reads the index of the pack `name`; `err` says why it cannot.
    bool read(std::string const & name, std::string & err) {
        fname = name;
        file_descriptor fd(open(fname.c_str(), O_RDONLY | O_CLOEXEC | O_NONBLOCK));
        if (!fd) { err = strerror(errno); return false; }
        struct stat st;
        if (fstat(fd.get(), &st) != 0 || !S_ISREG(st.st_mode) ||
            pread(fd.get(), &hdr, sizeof(hdr), 0) != static_cast<ssize_t>(sizeof(hdr))) {
            err = "cannot be read"; return false;
        }
        if (char const * why = check_side_file_header(hdr.common, g_pack_kind, sizeof(pack_header))) { err = why; return false; }
        if (hdr.format != g_pack_format || hdr.size != static_cast<uint64_t>(st.st_size) ||
            hdr.entries_off < g_pack_header_space || hdr.entries_off > hdr.size) {
            err = "not a pack of this version"; return false;
        }
        index.resize(hdr.size - hdr.entries_off);
        if (pread(fd.get(), index.data(), index.size(), hdr.entries_off) != static_cast<ssize_t>(index.size())) {
            err = "cannot be read"; return false;
        }
        if (pack_checksum(hdr, index.data(), index.size()) != hdr.common.checksum) { err = "corrupt (checksum mismatch)"; return false; }
        if (!pack_identity_ok(fname, hdr.common.checksum, st)) { err = "it changed since it was written"; return false; }
        auto in_index = [&](uint64_t off, uint64_t n, uint64_t elem) {
            return off >= hdr.entries_off && off <= hdr.size && n <= (hdr.size - off) / elem && off % 8 == 0;
        };
        if (!in_index(hdr.entries_off, hdr.num_entries, sizeof(pack_entry)) ||
            !in_index(hdr.chains_off, hdr.num_chains, sizeof(pack_chain)) ||
            !in_index(hdr.roots_off, hdr.num_roots, sizeof(pack_string)) ||
            !in_index(hdr.modules_off, hdr.num_modules, sizeof(pack_module)) ||
            !in_index(hdr.strings_off, hdr.strings_size, 1)) {
            err = "corrupt"; return false;
        }
        auto at = [&](uint64_t off) { return index.data() + (off - hdr.entries_off); };
        entries = reinterpret_cast<pack_entry const *>(at(hdr.entries_off));
        chains = reinterpret_cast<pack_chain const *>(at(hdr.chains_off));
        roots = reinterpret_cast<pack_string const *>(at(hdr.roots_off));
        modules = reinterpret_cast<pack_module const *>(at(hdr.modules_off));
        strings = at(hdr.strings_off);
        for (uint64_t i = 0; i < hdr.num_roots; i++) {
            if (!str_ok(roots[i])) { err = "corrupt"; return false; }
            root_paths.push_back(resolve_root(fname, str(roots[i])));
            root_fds.push_back(open(root_paths.back().c_str(), O_RDONLY | O_DIRECTORY | O_CLOEXEC));
        }
        return true;
    }

    // Whether a file of chain `c` changed since packing (as `check_chain_files` decides, apart from
    // its githash check).
    bool chain_changed(int32_t c) const {
        if (c < 0) return false;
        if (static_cast<uint64_t>(c) >= hdr.num_chains) return true;
        for (uint32_t i = chains[c].first; i < chains[c].first + chains[c].count && i < hdr.num_entries; i++) {
            pack_entry const & e = entries[i];
            char rel[PATH_MAX];
            struct stat fst;
            if (!str_ok(e.path) || e.path.len >= sizeof(rel) || e.root_idx >= root_fds.size() || root_fds[e.root_idx] < 0)
                return true;
            memcpy(rel, strings + e.path.off, e.path.len);
            rel[e.path.len] = 0;
            if (fstatat(root_fds[e.root_idx], rel, &fst, 0) != 0 || !same_file_id(e, fst)) return true;
        }
        return false;
    }
};
}
#endif

/* packStaleness (pack : @& String) : IO (Nat × Nat)
   For `paperlean status`: the number of modules of the pack whose files changed since packing (so that
   they are read from disk), and the number of its modules. Reads only the pack's index. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_pack_staleness(b_obj_arg opath) {
#if defined(LEAN_MMAP) && !defined(LEAN_WINDOWS)
    pack_index_file pf;
    std::string err;
    if (!pf.read(lean_string_cstr(opath), err))
        return io_result_mk_error(err.c_str());
    size_t stale = 0;
    for (uint64_t m = 0; m < pf.hdr.num_modules; m++)
        if (pf.chain_changed(pf.modules[m].olean_chain) || pf.chain_changed(pf.modules[m].ir_chain)) stale++;
    object * r = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(r, 0, lean_usize_to_nat(stale));
    lean_ctor_set(r, 1, lean_usize_to_nat(pf.hdr.num_modules));
    return io_result_mk_ok(r);
#else
    (void)opath;
    return io_result_mk_error("packStaleness: packs are not supported on this platform");
#endif
}

/* OLeanPack.whyIgnored (pack : @& String) : BaseIO String
   Why Lean ignores the pack `pack` as a whole, or "" if it does not, from its header and identity. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_pack_why_ignored(b_obj_arg opath) {
#if defined(LEAN_MMAP) && !defined(LEAN_WINDOWS)
    std::string path = lean_string_cstr(opath), err;
    file_descriptor fd(open(path.c_str(), O_RDONLY | O_CLOEXEC | O_NONBLOCK));
    struct stat st;
    pack_header hdr;
    read_pack_header(path, fd.get(), st, hdr, err);
    return mk_string(err);
#else
    (void)opath;
    return mk_string("");
#endif
}

/* OLeanPack.identityFile (pack : @& String) : String
   The file next to the pack `pack` that records its identity. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_pack_identity_file(b_obj_arg opath) {
#if defined(LEAN_MMAP) && !defined(LEAN_WINDOWS)
    return mk_string(pack_identity_path(lean_string_cstr(opath)));
#else
    (void)opath;
    return mk_string("");
#endif
}

/* OLeanPack.verify (pack : @& String) : IO String
   Why the olean pack `pack` cannot be used, or "" if it can and its index and regions are as written,
   which reads all of them. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_olean_pack_verify(b_obj_arg opath) {
#if defined(LEAN_MMAP) && !defined(LEAN_WINDOWS)
    try {
    pack_index_file pf;
    std::string err;
    if (!pf.read(lean_string_cstr(opath), err)) return io_result_mk_ok(mk_string(err));
    pack_tables t;
    if (pf.hdr.validated != g_pack_validated || pack_header_checksum(pf.hdr) != pf.hdr.header_checksum || !t.init_header(pf.hdr))
        return io_result_mk_ok(mk_string("corrupt"));
    t.set_tables(pf.index.data());
    uint64_t blocks_size = pf.hdr.block_sums_off - pf.hdr.entries_off;
    if (side_file_block_sums(pf.index.data(), blocks_size) !=
        std::string(pf.index.data() + blocks_size, pf.index.size() - blocks_size))
        return io_result_mk_ok(mk_string("corrupt (block checksums)"));
    if (char const * why = t.check_all()) return io_result_mk_ok(mk_string(why));
    file_descriptor fd(open(pf.fname.c_str(), O_RDONLY | O_CLOEXEC));
    if (!fd) return io_result_mk_ok(mk_string(strerror(errno)));
    uint64_t sum;
    if (int e = pack_payload_checksum(fd.get(), pf.hdr.entries_off, sum))
        return io_result_mk_ok(mk_string(strerror(e)));
    return io_result_mk_ok(mk_string(sum == pf.hdr.payload_checksum ? "" : "corrupt (its regions' checksum differs)"));
    } catch (std::exception & ex) {
        return io_result_mk_ok(mk_string(ex.what()));
    }
#else
    (void)opath;
    return io_result_mk_ok(mk_string("packs are not supported on this platform"));
#endif
}

/* packFreshFiles (packs : @& Array String) (root : @& String) : IO (Array String)
   The files below `root` (relative to it) that the packs `packs`, in this order, serve: Lean reads a
   file from the first of them that has it below a matching root, if its chain did not change since
   packing. A pack that cannot be read serves nothing. Reads only the packs' indexes. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_pack_fresh_files(b_obj_arg opacks, b_obj_arg oroot) {
    object * out = lean_alloc_array(0, 0);
#if defined(LEAN_MMAP) && !defined(LEAN_WINDOWS)
    std::string root = lean_string_cstr(oroot);
    while (root.size() > 1 && root.back() == '/') root.pop_back();
    std::unordered_set<std::string> decided;
    for (size_t pi = 0; pi < lean_array_size(opacks); pi++) {
        pack_index_file pf;
        std::string err;
        if (!pf.read(lean_string_cstr(lean_array_get_core(opacks, pi)), err)) continue;
        for (uint64_t c = 0; c < pf.hdr.num_chains; c++) {
            pack_chain const & ch = pf.chains[c];
            if (ch.count == 0 || ch.first >= pf.hdr.num_entries || ch.count > pf.hdr.num_entries - ch.first) continue;
            pack_entry const & first = pf.entries[ch.first];
            if (first.root_idx >= pf.root_paths.size() || pf.root_paths[first.root_idx] != root || !pf.str_ok(first.path))
                continue;
            if (!decided.insert(pf.str(first.path)).second) continue;
            std::vector<std::string> files;
            for (uint32_t i = ch.first; i < ch.first + ch.count; i++) {
                if (!pf.str_ok(pf.entries[i].path)) { files.clear(); break; }
                files.push_back(pf.str(pf.entries[i].path));
                decided.insert(files.back());
            }
            if (files.empty() || pf.chain_changed(static_cast<int32_t>(c))) continue;
            for (std::string const & f : files) out = lean_array_push(out, lean_mk_string(f.c_str()));
        }
    }
#else
    (void)opacks; (void)oroot;
#endif
    return io_result_mk_ok(out);
}

/* packsLoaded : BaseIO Bool */
extern "C" LEAN_EXPORT uint8_t lean_paperlean_packs_loaded() {
    std::call_once(g_packs_once, init_packs);
    return !g_packs.load(std::memory_order_acquire)->empty();
}

/* packNextImport : BaseIO Unit
   Starts an import: a process that imports again reads again what changed since the last one, as
   Lean does: the chains are checked again, and a root directory replaced meanwhile is opened again.
   (Before the packs are loaded, nothing has been checked.) */
extern "C" LEAN_EXPORT obj_res lean_paperlean_pack_next_import() {
    std::vector<loaded_pack> * packs = g_packs.load(std::memory_order_acquire);
    if (!packs) return lean_box(0);
    for (loaded_pack & p : *packs) {
        for (size_t r = 0; r < p.roots.size(); r++) {
            int error = 0;
            p.root_fds[r].store(root_dir_fd(p.roots[r], error, true), std::memory_order_relaxed);
        }
    }
    g_pack_generation.fetch_add(1, std::memory_order_acq_rel);
    return lean_box(0);
}

/* packJoin (wait : Bool) : BaseIO Bool
   With `wait`, whether no file of the chains that the fast import of this thread served before
   checking them (`serve_chain`) changed since packing, checking those that are not checked yet;
   forgets these chains. */
extern "C" LEAN_EXPORT uint8_t lean_paperlean_pack_join(uint8_t wait) {
    if (!t_unchecked) return true;
    unchecked_chains & u = *t_unchecked;
    bool ok = true;
    // from the last, while the validators check them from the first
    for (size_t k = u.chains.size(); wait && ok && k-- > 0;)
        ok = chain_unchanged(*u.chains[k].first, u.chains[k].second);
    if (wait && ok) {
        g_pack_served += u.served;
        g_pack_not_served += u.not_served;
    }
    u.chains.clear();
    u.queued = 0;
    u.importing = false;
    u.served = u.not_served = 0;
    return ok;
}

/* packBeginImport : BaseIO Unit
   Starts a fast import on this thread, which `packJoin` ends. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_pack_begin_import() {
    if (!t_unchecked) t_unchecked = new unchecked_chains();
    unchecked_chains & u = *t_unchecked;
    u.chains.clear();
    u.queued = 0;
    u.importing = true;
    u.served = u.not_served = 0;
    return lean_box(0);
}

/* packModuleNumEdges (m : UInt32) : UInt32 */
extern "C" LEAN_EXPORT uint32_t lean_paperlean_pack_module_num_edges(uint32_t id) {
    uint32_t idx;
    loaded_pack * p = pack_of(id, idx);
    return p ? p->modules[idx].num_edges : 0;
}

/* packModuleEdgeTarget (m j : UInt32) : UInt32
   The module imported by edge `j` of `m` if it is in the same pack. */
extern "C" LEAN_EXPORT uint32_t lean_paperlean_pack_module_edge_target(uint32_t id, uint32_t j) {
    uint32_t idx;
    loaded_pack * p = pack_of(id, idx);
    if (!p || j >= p->modules[idx].num_edges) return g_no_pack_module;
    pack_edge const & e = p->edges[p->modules[idx].first_edge + j];
    if (e.target < 0) return g_no_pack_module;
    uint8_t s = module_status(*g_packs.load(std::memory_order_acquire), id >> 24, static_cast<uint32_t>(e.target));
    if (!(s & module_valid) || !(s & module_here) || !(p->modules[e.target].flags & pack_module_edges))
        return g_no_pack_module;
    return (id & 0xff000000) | static_cast<uint32_t>(e.target);
}

/* packModuleEdgeFlags (m j : UInt32) : UInt8
   The fields `importAll`, `isExported` and `isMeta` of edge `j` of `m` as bits 0, 1 and 2. */
extern "C" LEAN_EXPORT uint8_t lean_paperlean_pack_module_edge_flags(uint32_t id, uint32_t j) {
    uint32_t idx;
    loaded_pack * p = pack_of(id, idx);
    lean_always_assert(p && j < p->modules[idx].num_edges);
    pack_edge const & e = p->edges[p->modules[idx].first_edge + j];
    return (e.import_all ? 1 : 0) | (e.is_exported ? 2 : 0) | (e.is_meta ? 4 : 0);
}

/* packModuleEdgeImport (m j : UInt32) : Import
   Edge `j` of `m` as an `Import` with the same fields as the module's `Import` object. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_pack_module_edge_import(uint32_t id, uint32_t j) {
    uint32_t idx;
    loaded_pack * p = pack_of(id, idx);
    lean_always_assert(p && j < p->modules[idx].num_edges);
    pack_edge const & e = p->edges[p->modules[idx].first_edge + j];
    object * imp = lean_alloc_ctor(0, 1, 3);
    lean_ctor_set(imp, 0, reinterpret_cast<object *>(e.module));
    lean_ctor_set_uint8(imp, sizeof(void *), e.import_all);
    lean_ctor_set_uint8(imp, sizeof(void *) + 1, e.is_exported);
    lean_ctor_set_uint8(imp, sizeof(void *) + 2, e.is_meta);
    return imp;
}

/* packModulePaths (m : UInt32) : Array String × Array String
   The paths of the packed `.olean` and IR files of `m`. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_pack_module_paths(uint32_t id) {
    uint32_t idx;
    loaded_pack * p = pack_of(id, idx);
    object * r = lean_alloc_ctor(0, 2, 0);
    for (int k = 0; k < 2; k++) {
        object * paths = lean_mk_empty_array();
        int32_t chain = p ? (k == 0 ? p->modules[idx].olean_chain : p->modules[idx].ir_chain) : -1;
        if (chain >= 0) {
            pack_chain const & c = p->chains[chain];
            for (uint32_t i = c.first; i < c.first + c.count; i++) {
                pack_entry const & e = p->entries[i];
                std::string path = p->roots[e.root_idx] + "/" +
                    std::string(p->begin + p->hdr.strings_off + e.path.off, e.path.len);
                paths = lean_array_push(paths, lean_mk_string_from_bytes(path.data(), path.size()));
            }
        }
        lean_ctor_set(r, k, paths);
    }
    return r;
}

/* packModulePackage (m : UInt32) : String × String
   The root of the files of `m` and its package (the first component of its name). */
extern "C" LEAN_EXPORT obj_res lean_paperlean_pack_module_package(uint32_t id) {
    uint32_t idx;
    loaded_pack * p = pack_of(id, idx);
    object * r = lean_alloc_ctor(0, 2, 0);
    if (!p) {
        lean_ctor_set(r, 0, lean_mk_string(""));
        lean_ctor_set(r, 1, lean_mk_string(""));
        return r;
    }
    pack_module const & m = p->modules[idx];
    std::string const & root = p->roots[m.root_idx];
    lean_ctor_set(r, 0, lean_mk_string_from_bytes(root.data(), root.size()));
    std::string_view stem(p->begin + p->hdr.strings_off + m.stem.off, m.stem.len);
    stem = stem.substr(0, stem.find('/'));
    lean_ctor_set(r, 1, lean_mk_string_from_bytes(stem.data(), stem.size()));
    return r;
}

/* packModuleIsModule (m : UInt32) : Bool
   `ModuleData.isModule` of the packed `.olean` of `m`. */
extern "C" LEAN_EXPORT uint8_t lean_paperlean_pack_module_is_module(uint32_t id) {
    uint32_t idx;
    loaded_pack * p = pack_of(id, idx);
    return p && (p->modules[idx].flags & pack_module_is_module);
}

/* packModuleParts (m : UInt32) (ir : Bool) (count : UInt32) :
     BaseIO (Option (Array (ModuleData × CompactedRegion)))
   The first `count` parts of the `.olean` or IR chain of `m` as `readModuleDataParts` reads them, if
   the chain is packed and that long, and not known to have changed: one not checked yet is checked
   by `packJoin`. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_pack_module_parts(uint32_t id, uint8_t ir, uint32_t count) {
    scoped_import_timer timer(counter_pack_parts);
    uint32_t idx;
    loaded_pack * p = pack_of(id, idx);
    if (!p) return lean_box(0);
    int32_t chain = ir ? p->modules[idx].ir_chain : p->modules[idx].olean_chain;
    if (chain < 0 || count == 0 || count > p->chains[chain].count || !serve_chain(*p, chain)) return lean_box(0);
    return mk_option_some(pack_chain_parts(*p, chain, count));
}

// =======================================
// `ModuleData` fields for `finalizeImport`, from the pack's metadata if the module data is packed

/* moduleDataIsModule (d : @& ModuleData) : Bool */
extern "C" LEAN_EXPORT uint8_t lean_paperlean_module_data_is_module(b_obj_arg d) {
    if (pack_part const * pp = import_legacy_mode() ? nullptr : packed_part(d)) return pp->is_module;
    return module_data_is_module(d);
}

/* moduleDataNumConstants (d : @& ModuleData) : Nat -- `d.constants.size` */
extern "C" LEAN_EXPORT obj_res lean_paperlean_module_data_num_constants(b_obj_arg d) {
    if (pack_part const * pp = import_legacy_mode() ? nullptr : packed_part(d)) return lean_usize_to_nat(pp->num_constants);
    return lean_usize_to_nat(lean_array_size(module_data_field(d, 2)));
}

/* moduleDataNumExtraConstNames (d : @& ModuleData) : Nat -- `d.extraConstNames.size` */
extern "C" LEAN_EXPORT obj_res lean_paperlean_module_data_num_extra_const_names(b_obj_arg d) {
    if (pack_part const * pp = import_legacy_mode() ? nullptr : packed_part(d)) return lean_usize_to_nat(pp->num_extra_const_names);
    return lean_usize_to_nat(lean_array_size(module_data_field(d, 3)));
}

bool packed_part_names(b_obj_arg d, part_names & out) {
    loaded_pack * p = nullptr;
    pack_part const * pp = packed_part(d, &p);
    if (!pp) return false;
    out.pack = p;
    size_t i = pp - p->parts;
    uint8_t state = p->names_state[i].load(std::memory_order_acquire);
    if (state == 0) {
        state = side_file_checksum(p->begin + pp->names, part_names_size(*pp)) == pp->names_checksum ? 1 : 2;
        p->names_state[i].store(state, std::memory_order_release);
    }
    if (state == 1) {
        out.hashes = reinterpret_cast<uint64_t const *>(p->begin + pp->names);
        out.single = out.hashes + pp->num_const_names + pp->num_extra_const_names;
        out.num_const_names = pp->num_const_names;
    }
    return true;
}

// The arrays `constNames`, `constants`, `extraConstNames` of `d`.
void module_data_arrays(b_obj_arg d, object ** names, object ** consts, object ** extra) {
    if (pack_part const * pp = packed_part(d)) {
        *names = reinterpret_cast<object *>(pp->const_names);
        *consts = reinterpret_cast<object *>(pp->constants);
        *extra = reinterpret_cast<object *>(pp->extra_const_names);
    } else {
        *names = module_data_field(d, 1);
        *consts = module_data_field(d, 2);
        *extra = module_data_field(d, 3);
    }
}

/* importedEntriesArrays (mods : @& Array ModuleData) (extNames : @& Array Name)
     (empty : @& Array EnvExtensionEntry) (persistent : Bool) : Array (Array (Array EnvExtensionEntry))
   For each name of `extNames`, the `importedEntries` that `setImportedEntries` builds for the
   extension of that name: per module, the entries of the last element of `mod.entries` with that
   name, or `empty`. With `persistent`, arrays of persistent entries are allocated persistent. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_imported_entries_arrays(b_obj_arg mods, b_obj_arg ext_names,
                                                                      b_obj_arg empty, uint8_t persistent) {
    size_t n = lean_array_size(mods);
    size_t k = lean_array_size(ext_names);
    // name hash -> extension indices with that hash
    std::unordered_multimap<uint64_t, uint32_t> by_hash;
    for (size_t e = 0; e < k; e++) by_hash.emplace(lean_name_hash(lean_array_get_core(ext_names, e)), static_cast<uint32_t>(e));
    auto ext_of = [&](b_obj_arg name) -> int64_t {
        auto r = by_hash.equal_range(lean_name_hash(name));
        int64_t found = -1;
        for (auto it = r.first; it != r.second; ++it)
            if (lean_name_eq(lean_array_get_core(ext_names, it->second), name)) found = it->second;
        return found;
    };
    // per pack, extension name id -> extension index (-2: not yet looked up)
    std::vector<std::pair<loaded_pack *, std::vector<int64_t>>> pack_maps;
    auto pack_map = [&](loaded_pack * p) -> std::vector<int64_t> & {
        for (auto & pm : pack_maps) if (pm.first == p) return pm.second;
        pack_maps.emplace_back(p, std::vector<int64_t>(p->hdr.num_ext_names, -2));
        return pack_maps.back().second;
    };
    std::vector<object *> arrays(k);
    for (size_t e = 0; e < k; e++) {
        lean_inc_n(empty, n);
        object * a = lean_alloc_array(n, n);
        for (size_t m = 0; m < n; m++) lean_array_cptr(a)[m] = empty;
        arrays[e] = a;
    }
    // Entries of packed parts are persistent; others are counted.
    bool all_persistent = lean_is_persistent(empty);
    auto set = [&](int64_t e, size_t m, object * entries, bool packed) {
        if (e < 0) return;
        object ** slot = lean_array_cptr(arrays[e]) + m;
        if (!packed) {
            lean_inc(entries);
            all_persistent = all_persistent && lean_is_persistent(entries);
        }
        if (*slot != empty) lean_dec(*slot); else if (!lean_is_persistent(empty)) lean_dec(empty);
        *slot = entries;
    };
    for (size_t m = 0; m < n; m++) {
        object * d = lean_array_get_core(mods, m);
        loaded_pack * p = nullptr;
        if (pack_part const * pp = packed_part(d, &p)) {
            std::vector<int64_t> & ids = pack_map(p);
            for (uint32_t j = pp->first_ext; j < pp->first_ext + pp->num_entries; j++) {
                pack_ext_entry const & ee = p->ext_entries[j];
                if (ids[ee.name] == -2) ids[ee.name] = ext_of(reinterpret_cast<object *>(p->ext_names[ee.name].name));
                set(ids[ee.name], m, reinterpret_cast<object *>(ee.entries), true);
            }
        } else {
            object * entries = module_data_field(d, 4);
            for (size_t j = 0; j < lean_array_size(entries); j++) {
                object * pair = lean_array_get_core(entries, j);
                set(ext_of(lean_ctor_get(pair, 0)), m, lean_ctor_get(pair, 1), false);
            }
        }
    }
    if (persistent && all_persistent)
        for (object * a : arrays) a->m_rc = 0;
    object * r = lean_alloc_array(k, k);
    for (size_t e = 0; e < k; e++) lean_array_cptr(r)[e] = arrays[e];
    return r;
}

}
