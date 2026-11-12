/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/

/*
Demand reads of Lake's immutable setup-index generations. The v1 index bytes and filename hash
remain unchanged. A small build-versioned receipt is published only after validating the complete
encoded index and comparing the completed regular read-only file against those exact bytes.
Readers bind the receipt to an open descriptor's full identity, not just its name. pread avoids
SIGBUS if an external process truncates a file; bounds are checked before each read and identity
is checked again before the resolved setup is returned. Missing/stale receipts select Lean's full
content-hash path. This is a normal filesystem identity contract, not an authentication boundary:
setups already specify authoritative artifact paths. Published generations are never overwritten.
*/
#include <algorithm>
#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <mutex>
#include <stdexcept>
#include <string>
#include <vector>
#include "runtime/object.h"
#include "runtime/io.h"
#include "runtime/hash.h"
#include "runtime/utf8.h"
#include "paperlean/olean_pack.h"
#include "paperlean/side_file.h"
#if !defined(LEAN_WINDOWS)
#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>
#endif

namespace lean {
namespace {
#if !defined(LEAN_WINDOWS)
constexpr char magic[] = "paperlean-setup-index 1\n";
constexpr char receipt_kind[] = "setup-index-id";
constexpr uint32_t no_module = 0xffffffffu;
constexpr uint32_t unknown_module = 0xfffffffeu;

struct descriptor {
    int fd = -1;
    explicit descriptor(int f = -1): fd(f) {}
    descriptor(descriptor const &) = delete;
    descriptor & operator=(descriptor const &) = delete;
    ~descriptor() { if (fd >= 0) close(fd); }
    int release() { int f = fd; fd = -1; return f; }
};

// (no device: see `file_identity` in `olean_pack.h`)
file_identity identity(struct stat const & s) {
#if defined(__APPLE__)
    return {0, static_cast<uint64_t>(s.st_ino),
        static_cast<uint64_t>(s.st_size), s.st_mtimespec.tv_sec, s.st_mtimespec.tv_nsec,
        s.st_ctimespec.tv_sec, s.st_ctimespec.tv_nsec};
#else
    return {0, static_cast<uint64_t>(s.st_ino),
        static_cast<uint64_t>(s.st_size), s.st_mtim.tv_sec, s.st_mtim.tv_nsec,
        s.st_ctim.tv_sec, s.st_ctim.tv_nsec};
#endif
}

bool regular(int fd, struct stat & st) {
    return fd >= 0 && fstat(fd, &st) == 0 && S_ISREG(st.st_mode) && st.st_size >= 0;
}

bool unchanged(int fd, std::string const & path, file_identity const & expected) {
    struct stat opened, named;
    return regular(fd, opened) && (opened.st_mode & 0222) == 0 && identity(opened) == expected &&
        lstat(path.c_str(), &named) == 0 && S_ISREG(named.st_mode) && named.st_dev == opened.st_dev &&
        identity(named) == expected;
}

int open_regular(std::string const & path) {
    return open(path.c_str(), O_RDONLY | O_CLOEXEC | O_NONBLOCK | O_NOFOLLOW);
}

// A nonblocking, readable descriptor for the final regular entry itself.
struct selected_regular {
    std::string path;
    descriptor file;
    struct stat opened;
    explicit selected_regular(char const * name) : path(name) {
        struct stat named;
        if (lstat(name, &named) != 0 || !S_ISREG(named.st_mode))
            throw std::runtime_error("not a regular file");
        file.fd = open_regular(path);
        if (!regular(file.fd, opened) || named.st_dev != opened.st_dev || !(identity(named) == identity(opened)))
            throw std::runtime_error("regular file changed before reading");
    }
    void check() const {
        struct stat after, named;
        if (!regular(file.fd, after) || after.st_dev != opened.st_dev || !(identity(opened) == identity(after)) ||
            lstat(path.c_str(), &named) != 0 || !S_ISREG(named.st_mode) || named.st_dev != opened.st_dev ||
            !(identity(opened) == identity(named)))
            throw std::runtime_error("regular file changed during reading");
    }
};

void read_at(int fd, uint64_t size, uint64_t pos, void * out, size_t n) {
    if (pos > size || n > size - pos) throw std::runtime_error("setup index is truncated");
    auto p = static_cast<unsigned char *>(out);
    for (size_t got = 0; got < n;) {
        size_t part = std::min<size_t>(n - got, 1u << 20);
        ssize_t r = pread(fd, p + got, part, static_cast<off_t>(pos + got));
        if (r < 0 && errno == EINTR) continue;
        if (r <= 0) throw std::runtime_error("setup index changed or could not be read");
        got += static_cast<size_t>(r);
    }
}

uint32_t u32(unsigned char const * p) {
    return static_cast<uint32_t>(p[0]) | (static_cast<uint32_t>(p[1]) << 8) |
        (static_cast<uint32_t>(p[2]) << 16) | (static_cast<uint32_t>(p[3]) << 24);
}

// Complete producer-side structural validation, with no per-module allocation.
struct cursor {
    unsigned char const * bytes;
    size_t pos, end;
    void need(size_t n) const {
        if (pos > end || n > end - pos) throw std::runtime_error("invalid setup index bounds");
    }
    uint32_t word() { need(4); uint32_t n = u32(bytes + pos); pos += 4; return n; }
    uint8_t byte() { need(1); return bytes[pos++]; }
    void text() {
        size_t n = word(); need(n);
        size_t p = 0, i = 0;
        if (!validate_utf8(bytes + pos, n, p, i)) throw std::runtime_error("invalid setup index UTF-8");
        pos += n;
    }
};

void validate(unsigned char const * bytes, size_t size) {
    constexpr size_t m = sizeof(magic) - 1;
    if (size < m || memcmp(bytes, magic, m) != 0) throw std::runtime_error("not a v1 setup index");
    cursor h{bytes, m, size};
    uint32_t roots = h.word();
    if (roots > (size - h.pos) / 4) throw std::runtime_error("invalid setup index roots");
    for (uint32_t i = 0; i < roots; ++i) h.text();
    uint32_t count = h.word();
    if (count > (size - h.pos) / 4) throw std::runtime_error("invalid setup index offset table");
    size_t table = h.pos, body = table + static_cast<size_t>(count) * 4;
    if (!count && body != size) throw std::runtime_error("trailing setup index data");
    for (uint32_t i = 0; i < count; ++i) {
        size_t from = u32(bytes + table + static_cast<size_t>(i) * 4);
        size_t to = i + 1 < count ? u32(bytes + table + static_cast<size_t>(i + 1) * 4) : size;
        if (from < body || to <= from || to > size || (i == 0 && from != body))
            throw std::runtime_error("invalid setup index record offsets");
        cursor r{bytes, from, to};
        uint32_t parts = r.word();
        if (parts > (to - r.pos) / 4) throw std::runtime_error("invalid setup index name");
        for (uint32_t j = 0; j < parts; ++j) r.text();
        if (r.word() >= roots || r.byte() > 1) throw std::runtime_error("invalid setup index module");
        uint32_t imports = r.word();
        if (imports > (to - r.pos) / 5 || r.pos + static_cast<size_t>(imports) * 5 != to)
            throw std::runtime_error("invalid setup index import bounds");
        for (uint32_t j = 0; j < imports; ++j) {
            uint32_t target = r.word();
            if ((target >= count && target != no_module && target != unknown_module) || r.byte() > 7)
                throw std::runtime_error("invalid setup index import");
        }
    }
}

struct receipt {
    side_file_header common;
    file_identity file;
    uint64_t content_hash;
};

uint64_t checksum(receipt value) {
    value.common.checksum = 0;
    return side_file_checksum(&value, sizeof(value));
}

std::string filename(uint64_t h) {
    char out[64];
    snprintf(out, sizeof(out), "setup-%llx.paperlean", static_cast<unsigned long long>(h));
    return out;
}

bool has_name(std::string const & path, uint64_t h) {
    size_t slash = path.rfind('/');
    return path.substr(slash == std::string::npos ? 0 : slash + 1) == filename(h);
}

// Owns only a newly created temporary name. Never removes an existing published file.
struct temporary {
    std::string path;
    descriptor file;
    explicit temporary(std::string const & target): path(target + ".tmp-XXXXXX") {
        std::vector<char> name(path.begin(), path.end()); name.push_back(0);
        file.fd = mkstemp(name.data());
        if (file.fd < 0) throw std::runtime_error("cannot create setup index temporary file");
        path = name.data();
        fcntl(file.fd, F_SETFD, FD_CLOEXEC);
    }
    ~temporary() { if (!path.empty()) unlink(path.c_str()); }
    void write(void const * data, size_t n) {
        auto p = static_cast<unsigned char const *>(data);
        for (size_t done = 0; done < n;) {
            ssize_t r = ::write(file.fd, p + done, std::min<size_t>(n - done, 1u << 20));
            if (r < 0 && errno == EINTR) continue;
            if (r <= 0) throw std::runtime_error("cannot write setup index temporary file");
            done += static_cast<size_t>(r);
        }
        if (fchmod(file.fd, 0444) != 0) throw std::runtime_error("cannot make setup index read-only");
    }
    void remove_name() {
        if (unlink(path.c_str()) != 0) throw std::runtime_error("cannot remove setup index temporary name");
        path.clear();
    }
};

void publish(std::string const & path, unsigned char const * bytes, size_t size) {
    validate(bytes, size);
    uint64_t hash = hash_str(size, bytes, 11);
    if (!has_name(path, hash)) throw std::runtime_error("setup index filename does not match its contents");
    temporary tmp(path);
    tmp.write(bytes, size);
    if (link(tmp.path.c_str(), path.c_str()) != 0 && errno != EEXIST)
        throw std::runtime_error("cannot publish setup index");
    tmp.remove_name();
    // Renames/links change ctime, so capture the final name only after publication and unlink.
    descriptor fd(open_regular(path));
    struct stat st;
    if (!regular(fd.fd, st) || (st.st_mode & 0222) != 0 || static_cast<uint64_t>(st.st_size) != size)
        throw std::runtime_error("published setup index is not the expected read-only file");
    file_identity id = identity(st);
    unsigned char block[65536];
    for (size_t p = 0; p < size;) {
        size_t n = std::min<size_t>(sizeof(block), size - p);
        read_at(fd.fd, size, p, block, n);
        if (memcmp(block, bytes + p, n) != 0) throw std::runtime_error("published setup index differs from encoded bytes");
        p += n;
    }
    if (!unchanged(fd.fd, path, id)) throw std::runtime_error("setup index changed during publication");
    if (fsync(fd.fd) != 0) throw std::runtime_error("cannot flush published setup index");
    // For small indices checking the content-addressed bytes in each reader is
    // cheaper than opening a receipt and seeking to individual records.
    // The generation itself is immutable and has been validated in both cases.
    if (id.size <= 128 * 1024) return;
    receipt r{};
    init_side_file_header(r.common, receipt_kind, sizeof(r));
    r.file = id; r.content_hash = hash; r.common.checksum = checksum(r);
    std::string out = path + ".validated";
    temporary record(out);
    record.write(&r, sizeof(r));
    if (fsync(record.file.fd) != 0) throw std::runtime_error("cannot flush setup index receipt");
    if (!unchanged(fd.fd, path, id)) throw std::runtime_error("setup index changed before receipt publication");
    if (rename(record.path.c_str(), out.c_str()) != 0) throw std::runtime_error("cannot publish setup index receipt");
    record.path.clear();
}

bool read_receipt(std::string const & path, receipt & out) {
    descriptor fd(open_regular(path + ".validated"));
    struct stat before, after;
    if (!regular(fd.fd, before) || static_cast<uint64_t>(before.st_size) != sizeof(out) || (before.st_mode & 0222) != 0) return false;
    try { read_at(fd.fd, sizeof(out), 0, &out, sizeof(out)); } catch (...) { return false; }
    if (!regular(fd.fd, after) || after.st_dev != before.st_dev || !(identity(before) == identity(after))) return false;
    return check_side_file_header(out.common, receipt_kind, sizeof(out)) == nullptr &&
        out.common.checksum == checksum(out) && has_name(path, out.content_hash);
}

struct reader {
    descriptor file;
    std::string path;
    file_identity id;
    uint64_t table = 0, bytes_read = 0, records_read = 0;
    uint32_t count = 0;
    std::mutex mutex;
    std::string events;
    reader(int fd, std::string p, file_identity i): file(fd), path(std::move(p)), id(i) {
        if (char const * e = getenv("PAPERLEAN_SETUP_INDEX_READS")) events = e;
    }
    void check() {
        if (!unchanged(file.fd, path, id)) throw std::runtime_error("setup index generation changed during demand reading");
    }
    void read(uint64_t pos, void * out, size_t n) {
        read_at(file.fd, id.size, pos, out, n); bytes_read += n;
    }
    uint32_t word(uint64_t pos) { unsigned char b[4]; read(pos, b, 4); return u32(b); }
    std::vector<unsigned char> header() {
        constexpr size_t m = sizeof(magic) - 1;
        unsigned char prefix[m + 4]; read(0, prefix, sizeof(prefix));
        if (memcmp(prefix, magic, m) != 0) throw std::runtime_error("not a v1 setup index");
        uint32_t roots = u32(prefix + m);
        uint64_t p = m + 4;
        if (p > id.size || roots > (id.size - p) / 4) throw std::runtime_error("invalid setup index roots");
        for (uint32_t i = 0; i < roots; ++i) {
            uint32_t n = word(p); p += 4;
            if (p > id.size || n > id.size - p) throw std::runtime_error("invalid setup index root bounds");
            p += n;
        }
        count = word(p); table = p + 4;
        if (table > id.size || count > (id.size - table) / 4) throw std::runtime_error("invalid setup index table");
        std::vector<unsigned char> result(static_cast<size_t>(table));
        read(0, result.data(), result.size());
        return result;
    }
    std::vector<unsigned char> record(size_t i) {
        check();
        if (i >= count) throw std::runtime_error("setup index has no requested record");
        uint64_t from = word(table + i * 4);
        uint64_t to = i + 1 < count ? word(table + (i + 1) * 4) : id.size;
        if (from < table + static_cast<uint64_t>(count) * 4 || to <= from || to > id.size)
            throw std::runtime_error("invalid setup index record bounds");
        std::vector<unsigned char> bytes(static_cast<size_t>(to - from));
        read(from, bytes.data(), bytes.size());
        ++records_read;
        return bytes;
    }
    void close() {
        if (file.fd < 0) return;
        ::close(file.fd); file.fd = -1;
        // Counts copied index bytes, not OS page traffic, total allocations or elapsed CPU time.
        if (!events.empty()) {
            if (FILE * f = fopen(events.c_str(), "a")) {
                fprintf(f, "%s\t%llu\t%llu\t%llu\n", path.c_str(),
                    static_cast<unsigned long long>(bytes_read),
                    static_cast<unsigned long long>(records_read), static_cast<unsigned long long>(id.size));
                fclose(f);
            }
        }
    }
    ~reader() { close(); }
};

void finalize(void * p) { delete static_cast<reader *>(p); }
void foreach(void *, b_obj_arg) {}
lean_external_class * reader_class() {
    static lean_external_class * c = lean_register_external_class(finalize, foreach);
    return c;
}

object * byte_array(std::vector<unsigned char> const & bytes) {
    object * result = lean_alloc_sarray(1, bytes.size(), bytes.size());
    if (!bytes.empty()) memcpy(lean_sarray_cptr(result), bytes.data(), bytes.size());
    return result;
}
#endif
}

// Read at most limit bytes from the same regular file observed before open. In
// particular an absent, generated, symlinked, or FIFO source cannot block a
// tentative layout or be confused with a selected input job.
extern "C" LEAN_EXPORT obj_res lean_paperlean_setup_read_regular(b_obj_arg file, size_t limit) {
    if (strlen(lean_string_cstr(file)) + 1 != lean_string_size(file)) return mk_embedded_nul_error(file);
#if defined(LEAN_WINDOWS)
    (void)limit;
    return io_result_mk_ok(lean_box(0));
#else
    try {
        selected_regular src(lean_string_cstr(file));
        uint64_t size = static_cast<uint64_t>(src.opened.st_size);
        std::vector<unsigned char> bytes(static_cast<size_t>(std::min<uint64_t>(size, limit)));
        read_at(src.file.fd, size, 0, bytes.data(), bytes.size());
        src.check();
        object * pair = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(pair, 0, lean_box_uint64(size));
        lean_ctor_set(pair, 1, byte_array(bytes));
        object * some = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(some, 0, pair);
        return io_result_mk_ok(some);
    } catch (std::exception const & e) { return io_result_mk_error(e.what()); }
#endif
}

// Unlike a pathname-only stat, this succeeds only if the actual descriptor
// is readable and still selects the same regular entry. Its 56 bytes can be
// passed directly to OLeanPack.readVerifiedOwnedBytes for a cold capture.
extern "C" LEAN_EXPORT obj_res lean_paperlean_readable_source_identity(b_obj_arg file) {
#if !defined(LEAN_WINDOWS) && defined(LEAN_MMAP)
    if (strlen(lean_string_cstr(file)) + 1 != lean_string_size(file)) return lean_box(0);
    uint16_t endian = 1;
    if (*reinterpret_cast<unsigned char *>(&endian) != 1) return lean_box(0);
    try {
        selected_regular src(lean_string_cstr(file));
        auto id = identity(src.opened);
        src.check();
        uint64_t fields[] = {id.dev, id.ino, id.size, static_cast<uint64_t>(id.mtime_sec),
            static_cast<uint64_t>(id.mtime_nsec), static_cast<uint64_t>(id.ctime_sec),
            static_cast<uint64_t>(id.ctime_nsec)};
        object * bytes = lean_alloc_sarray(1, sizeof(fields), sizeof(fields));
        memcpy(lean_sarray_cptr(bytes), fields, sizeof(fields));
        object * some = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(some, 0, bytes);
        return some;
    } catch (std::exception const &) {}
#endif
    (void)file;
    return lean_box(0);
}

extern "C" LEAN_EXPORT obj_res lean_paperlean_setup_index_publish(b_obj_arg file, b_obj_arg bytes) {
    if (strlen(lean_string_cstr(file)) + 1 != lean_string_size(file)) return mk_embedded_nul_error(file);
#if defined(LEAN_WINDOWS)
    (void)file; (void)bytes;
    return io_result_mk_ok(lean_box(0));
#else
    try {
        publish(lean_string_cstr(file), lean_sarray_cptr(bytes), lean_sarray_size(bytes));
        return io_result_mk_ok(lean_box(1));
    } catch (std::exception const & e) { return io_result_mk_error(e.what()); }
#endif
}

extern "C" LEAN_EXPORT obj_res lean_paperlean_setup_index_open(b_obj_arg file) {
    if (strlen(lean_string_cstr(file)) + 1 != lean_string_size(file)) return mk_embedded_nul_error(file);
#if defined(LEAN_WINDOWS)
    (void)file;
    return io_result_mk_ok(lean_box(0));
#else
    try {
        std::string path = lean_string_cstr(file);
        receipt rec{};
        if (!read_receipt(path, rec)) return io_result_mk_ok(lean_box(0));
        descriptor fd(open_regular(path));
        if (!unchanged(fd.fd, path, rec.file)) return io_result_mk_ok(lean_box(0));
        auto r = std::make_unique<reader>(fd.release(), path, rec.file);
        auto prefix = r->header();
        r->check();
        object * pair = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(pair, 0, lean_alloc_external(reader_class(), r.release()));
        lean_ctor_set(pair, 1, byte_array(prefix));
        object * some = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(some, 0, pair);
        return io_result_mk_ok(some);
    } catch (std::exception const & e) { return io_result_mk_error(e.what()); }
#endif
}

extern "C" LEAN_EXPORT obj_res lean_paperlean_setup_index_record(b_obj_arg index, b_obj_arg i) {
#if defined(LEAN_WINDOWS)
    (void)index; (void)i;
    return io_result_mk_error("demand setup indexes are unavailable");
#else
    try {
        if (!lean_is_scalar(i)) throw std::runtime_error("setup index record is out of range");
        auto r = static_cast<reader *>(lean_get_external_data(index));
        std::lock_guard<std::mutex> lock(r->mutex);
        return io_result_mk_ok(byte_array(r->record(lean_unbox(i))));
    } catch (std::exception const & e) { return io_result_mk_error(e.what()); }
#endif
}

extern "C" LEAN_EXPORT obj_res lean_paperlean_setup_index_check(b_obj_arg index) {
#if defined(LEAN_WINDOWS)
    (void)index;
    return io_result_mk_error("demand setup indexes are unavailable");
#else
    try {
        auto r = static_cast<reader *>(lean_get_external_data(index));
        std::lock_guard<std::mutex> lock(r->mutex);
        r->check();
        return io_result_mk_ok(lean_box(0));
    } catch (std::exception const & e) { return io_result_mk_error(e.what()); }
#endif
}

extern "C" LEAN_EXPORT obj_res lean_paperlean_setup_index_close(b_obj_arg index) {
#if !defined(LEAN_WINDOWS)
    auto r = static_cast<reader *>(lean_get_external_data(index));
    std::lock_guard<std::mutex> lock(r->mutex);
    r->close();
#else
    (void)index;
#endif
    return lean_box(0);
}
}
