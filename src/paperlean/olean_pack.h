/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#pragma once
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>
#include "runtime/compact.h"

namespace lean {
// A file served from an olean pack (`LEAN_OLEAN_PACK`).
struct pack_hit {
    char * begin;       // the region's copy of the file in the pack
    size_t size;
    size_t orig_base;   // the file's `base_addr`
    object * root;
    object * region_root; // the root that the region's data holds (`root` may be a copy of it)
};

// Whether the file `fname`, to be read with `deps` as the regions of the earlier parts of its
// module, is served from a pack.
bool find_in_packs(std::string const & fname, std::vector<region_view> const & deps, pack_hit & hit);
// Whether `addr` lies in a pack.
bool in_packs(void const * addr);

// The identity of a file, as packs, bindings, native library manifests and PaperLean's other prepared
// data record it: inode, size, modification and change times (seconds and nanoseconds). `dev` is always 0:
// a device number is not a property of the file but of the host's mount (on a network filesystem such as
// CephFS or NFS the same file has a different `st_dev` on each machine, and local device numbers can
// change across reboots), so it would make prepared data look changed on every other host. Without it a
// different file at the same path has the same identity only if it has the same inode, size and both times
// to the nanosecond; the change time is set by the kernel on every write, rename or `chmod` and cannot be
// set by users, so that takes a block-level clone of the filesystem, which has the same contents until a
// change (which sets a new change time). In-process comparisons of two live `stat` results also compare
// `st_dev` (`same_stat`).
struct file_identity {
    uint64_t dev, ino, size;
    int64_t mtime_sec, mtime_nsec, ctime_sec, ctime_nsec;
    bool operator==(file_identity const & o) const {
        return dev == o.dev && ino == o.ino && size == o.size && mtime_sec == o.mtime_sec &&
            mtime_nsec == o.mtime_nsec && ctime_sec == o.ctime_sec && ctime_nsec == o.ctime_nsec;
    }
};
// The identity of the file at `path`.
bool stat_identity(char const * path, file_identity & id);
// What packs and native library manifests know a file's contents by: two 64-bit hashes of its bytes
// by different functions.
struct content_hash {
    uint64_t lo, hi;
    bool operator==(content_hash const & o) const { return lo == o.lo && hi == o.hi; }
};
content_hash hash_content(void const * data, size_t size);
// The files of a module: `.olean`, `.olean.server`, `.olean.private`, `.ir.sig` and `.ir`.
enum module_file_kind : uint32_t { file_olean, file_olean_server, file_olean_private, file_ir_sig, file_ir, num_module_file_kinds };
// The kind of the file at `path` by its extension, or `num_module_file_kinds`.
uint32_t module_file_kind_of(std::string_view path);
// For native libraries (`native_libs.cpp`): if `data` is the root of a part of the packed module
// named `n`, so that an import got it from the pack, the contents of the module's files that the pack
// holds, by kind, provided none changed since packing (or binding) and the pack can serve all files
// that an import may read. A module file must have both IR files packed: an import reads them from
// disk otherwise.
bool packed_module_files(b_obj_arg n, b_obj_arg data, std::vector<std::pair<uint32_t, content_hash>> & files);

// For import images (`import_state.cpp`), which describe the packs of a process: the entries arrays
// of extension `ext_name` of all parts of the packs, the packs' checksums and address ranges, and a
// string that identifies an extension name.
struct pack_range { uint64_t checksum, base, size; };
void for_each_pack_ext_entries(b_obj_arg ext_name, std::function<void(object *)> const & f);
std::vector<pack_range> loaded_pack_ranges();
// The range of a loaded pack (`part_names::pack`), as `loaded_pack_ranges` gives it.
pack_range range_of_loaded_pack(void const * pack);
// For writing an import image: calls `f(pack index, hashes, count)` with the name table (the hashes
// of `constNames` and then of `extraConstNames`) of each part of each loaded pack whose table is valid.
void for_each_pack_name_table(std::function<void(size_t, uint64_t const *, size_t)> const & f);
// The range that `loaded_pack_ranges` would give for the pack or binding `path` of `LEAN_OLEAN_PACK`;
// false with `err` if Lean ignores the file as a whole.
bool pack_range_of_file(std::string const & path, pack_range & r, std::string & err);
// The import image that this process reads its own imports with, along with the packs that it
// reads them from where `LEAN_OLEAN_PACK` is not set (`OLeanPack.useForProcess`), if it does so.
char const * process_import_image();
void extension_name_key(b_obj_arg n, std::string & key);
// For writing an import image: why the index of a pack is not as its writer left it, if one is not
// (readers check only the entries they use).
char const * packs_damaged();

// In `library/module.cpp`: the `.olean` format and regions.
size_t olean_header_size();
size_t olean_header_base_addr_offset();
// The header flags of this build.
uint8_t olean_header_flags();
// Whether `h` starts an `.olean` header with this build's marker and flags; its version and base address.
bool olean_header_info(char const * h, uint8_t & version, size_t & base_addr);
// Whether the githash of the `.olean` header `h` is this build's `LEAN_GITHASH`.
bool olean_header_githash_matches(char const * h);
// Whether `lean_compacted_region_read` rejects files whose githash is not this build's (in builds with
// `CHECK_OLEAN_VERSION`).
bool olean_githash_checked();
// A `CompactedRegion` object.
object * mk_olean_region(b_obj_arg ofname, object * root, char * buffer, size_t base_addr, size_t full_sz, bool is_mmap);
}
