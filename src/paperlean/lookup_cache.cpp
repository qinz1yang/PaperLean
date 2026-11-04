/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include <atomic>
#include "runtime/object.h"
#include "runtime/thread.h"
#include "paperlean/fast_import.h"

// A cache of each thread for lookups of names in tables of the imported modules, which do not change
// (`Lean.PaperLean.cachedLookup`): an entry is keyed by the addresses of the name and of two tables and
// by the kind of lookup. It takes only persistent names (of imported modules and of compiled code)
// and only tables made persistent for a process-lifetime import. Transient imports own their tables
// even though their module names and constants are persistent objects of regions: retaining such a
// table would let a later cache clear or thread exit traverse a region that has already been freed.
// Region generations also invalidate borrowed names from transient imports before address reuse.

namespace lean {
namespace {
// incremented when a region is freed
std::atomic<size_t> g_regions_freed{0};

struct lookup_cache {
    static constexpr size_t size = 4096;
    static constexpr unsigned max_held = 8;
    struct entry { lean_object * t1; lean_object * t2; lean_object * n; size_t kind; lean_object * r; };
    entry m_tab[size] = {};
    lean_object * m_held[max_held] = {};
    unsigned m_num_held = 0;
    size_t m_regions_freed = 0;

    ~lookup_cache() { clear(); }
    void clear() {
        for (entry & e : m_tab)
            if (e.r) {
                lean_dec(e.r);
                e = entry{};
            }
        for (unsigned i = 0; i < m_num_held; i++) lean_dec(m_held[i]);
        m_num_held = 0;
    }
    static size_t slot(size_t kind, lean_object * t1, lean_object * t2, lean_object * n) {
        size_t x = (reinterpret_cast<size_t>(n) >> 3) ^ (reinterpret_cast<size_t>(t1) >> 1) ^
            (reinterpret_cast<size_t>(t2) << 7) ^ (kind << 56);
        x ^= x >> 31;
        x *= 0x9E3779B97F4A7C15ull;
        x ^= x >> 29;
        return x & (size - 1);
    }
    bool held(lean_object * t) const {
        if (lean_is_scalar(t)) return true;
        for (unsigned i = 0; i < m_num_held; i++)
            if (m_held[i] == t) return true;
        return false;
    }
    // makes the cache hold `t1` and `t2`, emptying it first if it holds too many tables
    void hold(lean_object * t1, lean_object * t2) {
        if (held(t1) && held(t2)) return;
        if (m_num_held + 2 > max_held) clear();
        for (lean_object * t : {t1, t2})
            if (!held(t)) {
                lean_inc(t);
                m_held[m_num_held++] = t;
            }
    }
};
MK_THREAD_LOCAL_GET_DEF(lookup_cache, get_lookup_cache_core);

lookup_cache & get_lookup_cache() {
    lookup_cache & c = get_lookup_cache_core();
    size_t freed = g_regions_freed.load(std::memory_order_acquire);
    if (c.m_regions_freed != freed) {
        c.clear();
        c.m_regions_freed = freed;
    }
    return c;
}

bool process_lifetime_table(b_obj_arg t) {
    return lean_is_scalar(t) || lean_is_persistent(t);
}

bool cacheable(b_obj_arg t1, b_obj_arg t2, b_obj_arg n) {
    return !lean_is_scalar(n) && lean_is_persistent(n) &&
        process_lifetime_table(t1) && process_lifetime_table(t2);
}
}
}

/* lookupProbe {τ τ' α : Type} (kind : UInt8) (t1 : @& τ) (t2 : @& τ') (n : @& Name) : Option α */
extern "C" LEAN_EXPORT lean_object * lean_paperlean_lookup_probe(uint8_t kind, lean_object * t1, lean_object * t2,
                                                                 lean_object * n) {
    if (!lean::cacheable(t1, t2, n)) return lean_box(0);
    auto const & e = lean::get_lookup_cache().m_tab[lean::lookup_cache::slot(kind, t1, t2, n)];
    if (e.n != n || e.t1 != t1 || e.t2 != t2 || e.kind != kind || !e.r) return lean_box(0);
    lean_inc(e.r);
    return e.r;
}

/* lookupStore {τ τ' α : Type} (kind : UInt8) (t1 : @& τ) (t2 : @& τ') (n : @& Name) (r : α) : α */
extern "C" LEAN_EXPORT lean_object * lean_paperlean_lookup_store(uint8_t kind, lean_object * t1, lean_object * t2,
                                                                 lean_object * n, lean_object * r) {
    if (!lean::cacheable(t1, t2, n)) return r;
    lean::lookup_cache & c = lean::get_lookup_cache();
    c.hold(t1, t2);
    auto & e = c.m_tab[lean::lookup_cache::slot(kind, t1, t2, n)];
    if (e.r) lean_dec(e.r);
    // The cache wrapper is bookkeeping, not work of the lookup.
    lean::uncounted_heartbeats uncounted;
    // `some r`
    lean_object * s = lean_alloc_ctor(1, 1, 0);
    lean_inc(r);
    lean_ctor_set(s, 0, r);
    e = {t1, t2, n, kind, s};
    return r;
}

/* Called when a compacted region is freed (`lean_compacted_region_free`). */
extern "C" LEAN_EXPORT void lean_paperlean_lookup_cache_region_freed() {
    lean::g_regions_freed.fetch_add(1, std::memory_order_release);
}
