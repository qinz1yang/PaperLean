/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#pragma once
#include <atomic>
#include <cstdarg>
#include <cstdint>
#include <cstddef>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <string>
#include <ctime>
#if defined(LEAN_MMAP) && !defined(LEAN_WINDOWS)
#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>
#endif
#include "githash.h"
#include "paperlean_build.h"

namespace lean {
/*
Side files (`*.paperlean`) hold optional data derived from `.olean` files, such as olean packs.
Deleting one never changes results. Each starts with `side_file_header`; a reader ignores a file
whose magic, kind or version it does not know, whose githash is not its own, or whose checksum
does not match, and every kind records the identity of the files it was derived from so that a
reader can ignore stale data.
*/

// The version of this source tree: its own version, then the upstream release it is compatible with.
// PaperLean's version (`paperlean/VERSION`): `<PaperLean version>-lean<Lean version>`
constexpr char g_paperlean_version[] = PAPERLEAN_VERSION;
// The build (`build_id.cmake`)
constexpr char g_paperlean_build[] = PAPERLEAN_BUILD;
// What side file headers record as the writer's version: `<version>+<build>`
constexpr char g_side_file_version[] = PAPERLEAN_VERSION "+" PAPERLEAN_BUILD;

struct side_file_header {
    char magic[16];        // "PAPERLEAN", padded with '\0'
    char kind[16];         // e.g. "olean-pack", padded with '\0'
    char version[64];      // `g_side_file_version` of the writer, padded with '\0'
    char githash[40];      // `LEAN_GITHASH` of the writer
    uint32_t header_size;  // size of the whole header of the kind, this part included
    uint32_t reserved;
    // `side_file_checksum` of the kind's header with this field zero, followed by the parts of the
    // file that the kind says it covers
    uint64_t checksum;
};
static_assert(sizeof(side_file_header) == 16 + 16 + 64 + 40 + 4 + 4 + 8, "side_file_header must be packed");

inline void init_side_file_header(side_file_header & h, char const * kind, uint32_t header_size) {
    memset(&h, 0, sizeof(h));
    memcpy(h.magic, "PAPERLEAN", 9);
    strncpy(h.kind, kind, sizeof(h.kind));
    strncpy(h.version, g_side_file_version, sizeof(h.version));
    strncpy(h.githash, LEAN_GITHASH, sizeof(h.githash));
    h.header_size = header_size;
}

// The reason a file with header `h` cannot be read as a side file of `kind` of this build, if any.
inline char const * check_side_file_header(side_file_header const & h, char const * kind, uint32_t header_size) {
    side_file_header ref;
    init_side_file_header(ref, kind, header_size);
    if (memcmp(h.magic, ref.magic, sizeof(h.magic)) != 0) return "not a PaperLean side file";
    if (memcmp(h.kind, ref.kind, sizeof(h.kind)) != 0) return "a different kind of side file";
    if (memcmp(h.version, ref.version, sizeof(h.version)) != 0 || h.header_size != header_size)
        return "written by a different version or build of PaperLean";
    if (memcmp(h.githash, ref.githash, sizeof(h.githash)) != 0) return "written by a different build of Lean";
    return nullptr;
}

// A warning of `lean` about side files (a line): appended to the file `PAPERLEAN_WARNINGS` if it is set,
// as the `paperlean` commands do for the Lake they run (and dropped if the file cannot be opened),
// else written to the standard error. (Lake keeps the standard error of `lean` in its traces and
// repeats it in later builds, official ones too.)
inline void side_file_warning(char const * fmt, ...) {
    char buf[1024];
    va_list ap;
    va_start(ap, fmt);
    int n = vsnprintf(buf, sizeof(buf), fmt, ap);
    va_end(ap);
    if (n < 0) return;
    size_t len = static_cast<size_t>(n) < sizeof(buf) ? static_cast<size_t>(n) : sizeof(buf) - 1;
    if (len == sizeof(buf) - 1) buf[len - 1] = '\n';
    char const * log = getenv("PAPERLEAN_WARNINGS");
    if (log && *log) {
        if (FILE * f = fopen(log, "a")) {
            fwrite(buf, 1, len, f);
            fclose(f);
            return;
        }
    }
    fwrite(buf, 1, len, stderr);
}

#if defined(LEAN_MMAP) && !defined(LEAN_WINDOWS)
#ifdef __APPLE__
#define LEAN_STAT_MTIM(st) (st).st_mtimespec
#define LEAN_STAT_CTIM(st) (st).st_ctimespec
#else
#define LEAN_STAT_MTIM(st) (st).st_mtim
#define LEAN_STAT_CTIM(st) (st).st_ctim
#endif

/*
Readers ignore an import image that no longer has the modification time its writer recorded in it:
the writer sets that time last, so that any later write to the file changes it.
*/
// The modification time a writer records: now, in even seconds, which every file system keeps.
inline int64_t side_file_mtime_now() {
    struct timespec now;
    clock_gettime(CLOCK_REALTIME, &now);
    return static_cast<int64_t>(now.tv_sec) & ~int64_t(1);
}
// Whether the file `st` has the modification time `sec`, `nsec`.
inline bool side_file_mtime_is(struct stat const & st, int64_t sec, int64_t nsec) {
    return LEAN_STAT_MTIM(st).tv_sec == sec && LEAN_STAT_MTIM(st).tv_nsec == nsec;
}
// Sets the modification time of the file `fd` to `sec`; whether it has that time then.
inline bool side_file_set_mtime(int fd, int64_t sec) {
    struct timespec times[2] = { { 0, UTIME_OMIT }, { static_cast<time_t>(sec), 0 } };
    struct stat st;
    return futimens(fd, times) == 0 && fstat(fd, &st) == 0 && side_file_mtime_is(st, sec, 0);
}
// Writes the data of `fd` to the disk before what is written after it, such as a new name of the
// file. On macOS, whose `fsync` leaves the data in the drive's cache, where later writes may
// overtake it, `F_BARRIERFSYNC` orders them, as `F_FULLFSYNC` would at a much higher cost.
inline bool side_file_sync(int fd) {
#ifdef F_BARRIERFSYNC
    if (fcntl(fd, F_BARRIERFSYNC) == 0) return true;
#endif
#ifdef F_FULLFSYNC
    if (fcntl(fd, F_FULLFSYNC) == 0) return true;
#endif
    return fsync(fd) == 0;
}
#endif

// A fast 64-bit hash of `n` bytes, continuing from `h`, for side file checksums.
inline uint64_t side_file_checksum(void const * data, size_t n, uint64_t h = 0x50415045524c45ull) {
    unsigned char const * p = static_cast<unsigned char const *>(data);
    constexpr uint64_t k = 0x9e3779b97f4a7c15ull;
    for (; n >= 8; n -= 8, p += 8) {
        uint64_t w;
        memcpy(&w, p, 8);
        h = (h ^ w) * k;
        h ^= h >> 29;
    }
    uint64_t w = n;
    for (size_t i = 0; i < n; i++) w ^= static_cast<uint64_t>(p[i]) << (8 * (i + 1) % 64);
    h = (h ^ w) * k;
    return h ^ (h >> 32);
}

// `side_file_checksum`'s steps in four interleaved lanes, about four times as fast, for blocks.
inline uint64_t side_file_checksum4(void const * data, size_t n, uint64_t h) {
    unsigned char const * p = static_cast<unsigned char const *>(data);
    constexpr uint64_t k = 0x9e3779b97f4a7c15ull;
    uint64_t lanes[4] = { h, h + 1, h + 2, h + 3 };
    for (; n >= 32; n -= 32, p += 32) {
        for (unsigned l = 0; l < 4; l++) {
            uint64_t w;
            memcpy(&w, p + 8 * l, 8);
            lanes[l] = (lanes[l] ^ w) * k;
            lanes[l] ^= lanes[l] >> 29;
        }
    }
    return side_file_checksum(p, n, side_file_checksum(lanes, sizeof(lanes), h));
}

/*
An area of a side file whose blocks of `g_side_file_block` bytes have checksums
(`side_file_block_sums`) in a table of the file, which a reader checks once per process: a block is
checked when it is first used, so that a process reads and checks only the blocks it uses.
*/
constexpr uint64_t g_side_file_block = 4096;
inline uint64_t side_file_num_blocks(uint64_t size) { return (size + g_side_file_block - 1) / g_side_file_block; }
inline uint64_t side_file_block_sum(char const * area, uint64_t size, uint64_t b) {
    uint64_t from = b * g_side_file_block;
    uint64_t n = size - from < g_side_file_block ? size - from : g_side_file_block;
    return side_file_checksum4(area + from, n, 0x626c6f636bull + b);
}
// The checksums of the blocks of the `size` bytes at `area`, as a table.
inline std::string side_file_block_sums(char const * area, uint64_t size) {
    std::string sums;
    for (uint64_t b = 0; b < side_file_num_blocks(size); b++) {
        uint64_t sum = side_file_block_sum(area, size, b);
        sums.append(reinterpret_cast<char const *>(&sum), sizeof(sum));
    }
    return sums;
}

class side_file_blocks {
    char const * m_area = nullptr;
    uint64_t m_size = 0;
    uint64_t const * m_sums = nullptr;
    // per block: 0 = not yet checked, 1 = as written, 2 = damaged
    std::unique_ptr<std::atomic<uint8_t>[]> m_state;
public:
    // The area of `size` bytes at `area`, with the table `sums` of its blocks' checksums.
    void init(char const * area, uint64_t size, uint64_t const * sums) {
        m_area = area; m_size = size; m_sums = sums;
        m_state.reset(new std::atomic<uint8_t>[side_file_num_blocks(size)]());
    }
    bool empty() const { return !m_area; }
    // Whether the `n` bytes at `p` lie in the area and are as written.
    bool ok(void const * p, uint64_t n) const {
        uint64_t off = reinterpret_cast<uintptr_t>(p) - reinterpret_cast<uintptr_t>(m_area);
        if (reinterpret_cast<uintptr_t>(p) < reinterpret_cast<uintptr_t>(m_area) || off > m_size || n > m_size - off)
            return false;
        if (n == 0) return true;
        for (uint64_t b = off / g_side_file_block; b <= (off + n - 1) / g_side_file_block; b++) {
            uint8_t state = m_state[b].load(std::memory_order_acquire);
            if (state == 0) {
                state = side_file_block_sum(m_area, m_size, b) == m_sums[b] ? 1 : 2;
                m_state[b].store(state, std::memory_order_release);
            }
            if (state != 1) return false;
        }
        return true;
    }
};
}
