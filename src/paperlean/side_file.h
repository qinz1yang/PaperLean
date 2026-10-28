/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#pragma once
#include <cstdint>
#include <cstddef>
#include <cstring>
#include <string>
#include "githash.h"

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

struct side_file_header {
    char magic[16];        // "PAPERLEAN", padded with '\0'
    char kind[16];         // e.g. "olean-pack", padded with '\0'
    char version[64];      // `g_paperlean_version` of the writer, padded with '\0'
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
    strncpy(h.version, g_paperlean_version, sizeof(h.version));
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
        return "written by a different version of PaperLean";
    if (memcmp(h.githash, ref.githash, sizeof(h.githash)) != 0) return "written by a different build of Lean";
    return nullptr;
}

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
}
