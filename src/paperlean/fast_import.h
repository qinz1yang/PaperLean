/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#pragma once
#include <chrono>
#include <cstdint>
#include <lean/lean.h>
#include "runtime/alloc.h"

namespace lean {
// Counters of `PAPERLEAN_IMPORT_TIMING`, reported and reset with the next import timing mark.
enum import_counter { counter_region_read, counter_pack_lookup, counter_pack_validate, counter_pack_parts,
                      counter_pack_find, counter_prefetch_wait, num_import_counters };

// The arrays `constNames`, `constants` and `extraConstNames` of module data `d`, read from the olean
// pack's metadata without touching `d` if `d` is packed.
void module_data_arrays(lean_object * d, lean_object ** names, lean_object ** consts, lean_object ** extra);

// The name table of a packed part (`pack_part::names` in `module.cpp`).
struct part_names {
    void const * pack = nullptr;          // the part's pack
    uint64_t const * hashes = nullptr;    // `nullptr` if the table failed its checksum
    uint64_t const * single = nullptr;
    size_t num_const_names = 0;           // the hashes of `extraConstNames` follow
    // Whether no other module of the pack, and no other of the two arrays and no other element of
    // the same array of this module, has a name with the hash of name `k` of the table.
    bool is_single(size_t k) const { return (single[k / 64] >> (k % 64)) & 1; }
};
// Whether `d` is a packed part, all of whose objects are persistent; if so, its name table.
bool packed_part_names(lean_object * d, part_names & names);

// While it lives, allocations (of PaperLean's own bookkeeping) are not counted as heartbeats of the
// thread: PaperLean never counts more heartbeats than Lean.
class uncounted_heartbeats {
    uint64_t m_saved;
public:
    uncounted_heartbeats() : m_saved(get_num_heartbeats()) {}
    ~uncounted_heartbeats() { set_heartbeats(m_saved); }
};

bool import_timing_enabled();
// Reports the cost of the import step `phase` that just ended if import timing is enabled.
void import_timing_mark(char const * phase);
// `PAPERLEAN_IMPORT=legacy`
bool import_legacy_mode();
// `PAPERLEAN_IMPORT=check`
bool import_check_mode();
// `PAPERLEAN_HEARTBEATS=lean`: the optimizations that lower heartbeat counts while elaborating (native
// libraries, the interpreters' shared entries) are off, so that counts are Lean's.
bool lean_heartbeats_mode();
void import_timing_add(import_counter c, uint64_t ns);

// Adds the wall time of its scope to a counter if import timing is enabled.
class scoped_import_timer {
    import_counter m_counter;
    uint64_t m_start = 0;
    static uint64_t now() {
        return std::chrono::duration_cast<std::chrono::nanoseconds>(
            std::chrono::steady_clock::now().time_since_epoch()).count();
    }
public:
    explicit scoped_import_timer(import_counter c) : m_counter(c) {
        if (import_timing_enabled()) m_start = now();
    }
    ~scoped_import_timer() {
        if (m_start) import_timing_add(m_counter, now() - m_start);
    }
};
}
