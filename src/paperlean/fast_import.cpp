/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include <algorithm>
#include <vector>
#include <atomic>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <chrono>
#include <time.h>
#ifndef LEAN_WINDOWS
#include <sys/resource.h>
#endif
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "runtime/thread.h"
#include "paperlean/fast_import.h"

/*
Faster steps of `Lean.importModules`, called from `Lean/PaperLean/Import.lean`. Every function here
produces exactly the objects that the corresponding fold in `Lean/Environment.lean` produces;
`PAPERLEAN_IMPORT=legacy` selects the folds instead, and `PAPERLEAN_IMPORT=check` runs both and
compares the results.
*/

namespace lean {
extern "C" uint8 lean_paperlean_import_resolve_duplicate(obj_arg map, obj_arg cinfo, obj_arg prev,
                                                          uint8 check_error);

// =======================================
// Mode and phase timing

namespace {
uint8 read_import_mode() {
    char const * m = getenv("PAPERLEAN_IMPORT");
    if (!m) return 0;
    if (strcmp(m, "legacy") == 0) return 1;
    if (strcmp(m, "check") == 0) return 2;
    return 0;
}
uint8 g_import_mode = read_import_mode();

struct timing_point { double wall_ms, cpu_ms; long minflt; };
timing_point timing_now() {
#ifdef LEAN_WINDOWS
    // wall time only
    double ms = std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now().time_since_epoch()).count();
    return { ms, ms, 0 };
#else
    timespec w, c;
    clock_gettime(CLOCK_MONOTONIC, &w);
    // (of the process: the marks come from several threads, and have one baseline)
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &c);
    rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    return { w.tv_sec * 1e3 + w.tv_nsec / 1e6, c.tv_sec * 1e3 + c.tv_nsec / 1e6, ru.ru_minflt };
#endif
}
bool g_import_timing = getenv("PAPERLEAN_IMPORT_TIMING") != nullptr;
timing_point g_last_timing = timing_now();
}

namespace {
// `Lean.PaperLean.builtinRegistrationsDeferred`: set only by the `lean` executable around
// `lean_initialize` (`src/util/shell.cpp`), cleared by `flushBuiltinRegistrations`.
std::atomic<bool> g_defer_builtin_registrations{false};
}

/* builtinRegistrationsDeferred : BaseIO Bool */
extern "C" LEAN_EXPORT uint8 lean_paperlean_builtin_registrations_deferred() {
    return g_defer_builtin_registrations.load(std::memory_order_acquire);
}

/* endBuiltinRegistrationDeferral : BaseIO Unit */
extern "C" LEAN_EXPORT obj_res lean_paperlean_end_builtin_registration_deferral() {
    g_defer_builtin_registrations.store(false, std::memory_order_release);
    return lean_box(0);
}

// Called by the `lean` executable before it initializes Lean's library.
extern "C" LEAN_EXPORT void lean_paperlean_defer_builtin_registrations() {
    g_defer_builtin_registrations.store(true, std::memory_order_release);
}

/* importMode : BaseIO UInt8 -- 0: fast, 1: legacy, 2: check */
extern "C" LEAN_EXPORT uint8 lean_paperlean_import_mode() {
    return g_import_mode;
}

/* importTimingEnabled : BaseIO Bool */
extern "C" LEAN_EXPORT uint8 lean_paperlean_import_timing_enabled() {
    return g_import_timing;
}

namespace {
uint64_t g_counter_ns[num_import_counters];
uint64_t g_counter_calls[num_import_counters];
char const * const g_counter_names[num_import_counters] = { "regionRead", "packLookup", "packValidate", "packParts",
                                                             "packFind", "prefetchWait" };

void timing_mark(char const * phase) {
    if (g_import_timing) {
        timing_point t = timing_now();
        fprintf(stderr, "paperlean-timing %s wall=%.3f cpu=%.3f minflt=%ld\n", phase,
                t.wall_ms - g_last_timing.wall_ms, t.cpu_ms - g_last_timing.cpu_ms, t.minflt - g_last_timing.minflt);
        for (unsigned c = 0; c < num_import_counters; c++) {
            if (g_counter_calls[c])
                fprintf(stderr, "paperlean-counter %s.%s calls=%llu wall=%.3f\n", phase, g_counter_names[c],
                        static_cast<unsigned long long>(g_counter_calls[c]), g_counter_ns[c] / 1e6);
            g_counter_calls[c] = g_counter_ns[c] = 0;
        }
        g_last_timing = timing_now();
    }
}
}

bool import_timing_enabled() { return g_import_timing; }

void import_timing_mark(char const * phase) { timing_mark(phase); }

bool import_legacy_mode() { return g_import_mode == 1; }

bool import_check_mode() { return g_import_mode == 2; }

void import_timing_add(import_counter c, uint64_t ns) {
    g_counter_ns[c] += ns;
    g_counter_calls[c]++;
}

/* uncountedHeartbeats {α} (act : IO α) : IO α */
extern "C" LEAN_EXPORT obj_res lean_paperlean_uncounted_heartbeats(obj_arg act) {
    uncounted_heartbeats uncounted;
    return apply_1(act, io_mk_world());
}

/* uncounted5 {α β γ δ ε ζ} (f : @& α → β → γ → δ → ε → ζ) (a : @& α) (b : @& β) (c : @& γ)
   (d : @& δ) (e : @& ε) : ζ */
extern "C" LEAN_EXPORT obj_res lean_paperlean_uncounted5(b_obj_arg f, b_obj_arg a, b_obj_arg b,
                                                         b_obj_arg c, b_obj_arg d, b_obj_arg e) {
    uncounted_heartbeats uncounted;
    lean_inc(f); lean_inc(a); lean_inc(b); lean_inc(c); lean_inc(d); lean_inc(e);
    return lean_apply_5(f, a, b, c, d, e);
}

/* uncounted {α β γ δ} (f : α → β → γ → δ) (a : α) (b : β) (c : γ) : δ */
extern "C" LEAN_EXPORT obj_res lean_paperlean_uncounted(obj_arg f, obj_arg a, obj_arg b,
                                                        obj_arg c) {
    uncounted_heartbeats uncounted;
    return apply_3(f, a, b, c);
}

/* With `PAPERLEAN_IMPORT_TIMING`, the wall-clock time (seconds since the epoch) at which this process
   reached `phase`, to compare with the time a caller saw it end (e.g. the time after its outputs are
   written). */
void timing_epoch_mark(char const * phase) {
    if (!g_import_timing) return;
    timespec r;
    clock_gettime(CLOCK_REALTIME, &r);
    fprintf(stderr, "paperlean-epoch %s realtime=%.6f\n", phase, r.tv_sec + r.tv_nsec / 1e9);
    fflush(stderr);
}

/* epochMark (phase : @& String) : BaseIO Unit */
extern "C" LEAN_EXPORT obj_res lean_paperlean_epoch_mark(b_obj_arg phase) {
    timing_epoch_mark(lean_string_cstr(phase));
    return lean_box(0);
}

/* importTimingMark (phase : @& String) : BaseIO Unit
   Reports the time since the previous mark on stderr if `PAPERLEAN_IMPORT_TIMING` is set. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_import_timing_mark(b_obj_arg phase) {
    timing_mark(lean_string_cstr(phase));
    return lean_box(0);
}

// =======================================
// Constant maps
//
// The result is the exact object graph that the fold in `finalizeImport` builds with
// `Std.HashMap.getThenInsertIfNew?`, `insert` and `insertIfNew`: the same bucket array, every
// bucket list holding the same keys and values in the same order (most recently inserted first).
//
// Runtime representation (see the compiled `Std.DHashMap.Internal.Raw₀`): a `Std.HashMap` is the
// `Raw` constructor (tag 0) with the fields `size : Nat` and `buckets : Array (AssocList α β)`;
// `AssocList.nil` is `box(0)` and `AssocList.cons key value tail` is constructor 1 with three
// fields. The bucket of a key with hash `h` is `scrambleHash h &&& (buckets.size - 1)`.
//
// Duplicates are found by walking the bucket list with `lean_name_eq` (`Name.beq`, which compares
// the stored hashes first). A duplicate constant is resolved by `subsumesInfo` on the partial map,
// as in the fold. The time goes into page faults and cache misses on the names and the bucket arrays,
// so names of packed parts are not read: the pack's name tables give their hashes and tell which
// names cannot have an equal key in the map, and constants are processed in batches that first
// prefetch their buckets.

namespace {
inline size_t bucket_of(size_t nbuckets, uint64_t h) {
    uint64_t fold = h ^ (h >> 32);
    return static_cast<size_t>(fold ^ (fold >> 16)) & (nbuckets - 1);
}

// `Std.HashMap.emptyWithCapacity capacity`: `Nat.nextPowerOfTwo (capacity * 4 / 3)` empty buckets.
object * mk_empty_map(size_t capacity) {
    size_t n = capacity / 3 * 4 + capacity % 3 * 4 / 3;
    size_t buckets = 1;
    while (buckets < n) buckets *= 2;
    object * raw = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(raw, 0, lean_box(0));
    lean_ctor_set(raw, 1, lean_mk_array(lean_usize_to_nat(buckets), lean_box(0)));
    return raw;
}

// Builds into an empty map made by `mk_empty_map` whose bucket count already is final
// (`finalizeImport` creates the maps with the capacity of all entries, so they never grow).
class map_builder {
    object * m_raw;
    object ** m_slots;
    size_t m_nbuckets;
    size_t m_size = 0;
    // Nodes are allocated persistent, which requires that keys and values are persistent too.
    bool m_persistent;
    // Whether references to keys and values are counted; not if they are all persistent.
    bool m_count;
public:
    map_builder(object * raw, bool persistent, bool count) :
        m_raw(raw), m_persistent(persistent), m_count(count) {
        object * buckets = lean_ctor_get(raw, 1);
        m_slots = lean_array_cptr(buckets);
        m_nbuckets = lean_array_size(buckets);
    }
    // Whether a map of `capacity` takes `expected` entries without growing: `expandIfNecessary`
    // fires when `numBucketsForCapacity size > buckets.size`.
    static bool fits(size_t capacity, size_t expected) {
        return capacity <= (static_cast<size_t>(1) << 40) && expected <= capacity;
    }
    size_t bucket(uint64_t h) const { return bucket_of(m_nbuckets, h); }
    void prefetch(size_t i) const { __builtin_prefetch(m_slots + i, 1); }
    // After `prefetch`, the first node of bucket `i`; then its key.
    void prefetch_head(size_t i) const {
        object * n = m_slots[i];
        if (!lean_is_scalar(n)) __builtin_prefetch(n);
    }
    void prefetch_key(size_t i) const {
        object * n = m_slots[i];
        if (!lean_is_scalar(n)) __builtin_prefetch(lean_ctor_get(n, 0));
    }
    // A completed map is persistent if its nodes are.
    void finish() {
        if (m_persistent) {
            lean_ctor_get(m_raw, 1)->m_rc = 0;
            m_raw->m_rc = 0;
        }
    }
    object * find(size_t i, object * key) const {
        for (object * n = m_slots[i]; !lean_is_scalar(n); n = lean_ctor_get(n, 2))
            if (lean_name_eq(lean_ctor_get(n, 0), key))
                return n;
        return nullptr;
    }
    // `AssocList.cons key val` at the head of bucket `i`.
    void cons(size_t i, object * key, object * val) {
        if (m_count) { lean_inc(key); lean_inc(val); }
        object * n = lean_alloc_ctor(1, 3, 0);
        lean_ctor_set(n, 0, key);
        lean_ctor_set(n, 1, val);
        lean_ctor_set(n, 2, m_slots[i]);
        if (m_persistent) n->m_rc = 0;
        m_slots[i] = n;
        m_size++;
    }
    // `AssocList.replace`: the node keeps its place and takes the new key and value.
    void replace(object * n, object * key, object * val) {
        if (m_count) {
            lean_inc(key); lean_inc(val);
            lean_dec(lean_ctor_get(n, 0)); lean_dec(lean_ctor_get(n, 1));
        }
        lean_ctor_set(n, 0, key);
        lean_ctor_set(n, 1, val);
    }
    // Gives back persistent nodes to reference counting, e.g. when the map is not going to be kept:
    // each node is referenced exactly once, by its bucket or by the node before it.
    void unpersist() {
        if (m_persistent)
            for (size_t i = 0; i < m_nbuckets; i++)
                for (object * n = m_slots[i]; !lean_is_scalar(n); n = lean_ctor_get(n, 2))
                    n->m_rc = 1;
        m_persistent = false;
    }
    size_t count() const { return m_size; }
    void set_count(size_t n) { m_size = n; }
    size_t num_buckets() const { return m_nbuckets; }
    // Makes the map a valid map of the entries so far.
    object * sync() {
        lean_object * old = lean_ctor_get(m_raw, 0);
        lean_ctor_set(m_raw, 0, lean_usize_to_nat(m_size));
        lean_dec(old);
        return m_raw;
    }
};

constexpr size_t g_batch = 64;

// A set of hashes (open addressing; the hash 0 is kept apart).
class hash_set {
    std::vector<uint64_t> m_slots;
    size_t m_size = 0;
    bool m_zero = false;
    size_t slot(uint64_t h) const { return (h * 0x9e3779b97f4a7c15ull >> 20) & (m_slots.size() - 1); }
public:
    hash_set() : m_slots(16, 0) {}
    void insert(uint64_t h) {
        if (h == 0) { m_zero = true; return; }
        if (2 * (m_size + 1) > m_slots.size()) {
            std::vector<uint64_t> old(2 * m_slots.size(), 0);
            old.swap(m_slots);
            m_size = 0;
            for (uint64_t o : old) if (o) insert(o);
        }
        size_t i = slot(h);
        while (m_slots[i] != 0 && m_slots[i] != h) i = (i + 1) & (m_slots.size() - 1);
        if (m_slots[i] == 0) { m_slots[i] = h; m_size++; }
    }
    bool contains(uint64_t h) const {
        if (h == 0) return m_zero;
        for (size_t i = slot(h); m_slots[i] != 0; i = (i + 1) & (m_slots.size() - 1))
            if (m_slots[i] == h) return true;
        return false;
    }
};

// The value of `trusted_pack` with which name sources trust the packs of the import image in use.
char const g_image_packs_trusted_tag = 0;
void const * const g_image_packs_trusted = &g_image_packs_trusted_tag;

// The names one module data contributes: their hashes come from its pack's name table if the table
// is trusted. Without an import image, that holds for the parts of a single pack, the first one met.
// With an import image, it holds for the parts of all packs that the image describes (and only for
// them): the image records the hashes that occur in more than one of these packs. A name of a trusted
// table that `is_single` in it (and, with the image, whose hash is in no other of its packs) can only
// have an equal key in the map if some untrusted name has its hash; the hashes of all untrusted names
// are collected beforehand.
struct name_source {
    object * m_names;
    part_names m_table;
    bool m_trusted = false;
    bool m_packed = false;
    bool m_image = false;   // trusted as a pack of the import image
    size_t m_offset = 0;    // index of `m_names[0]` in the table
    name_source(object * data, object * names, bool extra, void const *& trusted_pack) : m_names(names) {
        m_packed = packed_part_names(data, m_table);
        if (!m_packed || !m_table.hashes) return;
        if (trusted_pack == g_image_packs_trusted) {
            m_image = m_trusted = image_covers_pack(m_table.pack);
        } else if (!trusted_pack || trusted_pack == m_table.pack) {
            trusted_pack = m_table.pack;
            m_trusted = true;
        }
        if (m_trusted) m_offset = extra ? m_table.num_const_names : 0;
    }
    uint64_t hash(size_t k) const {
        return m_trusted ? m_table.hashes[m_offset + k] : lean_name_hash(lean_array_get_core(m_names, k));
    }
    // Whether name `k`, of hash `h`, cannot have an equal key in the map.
    bool fresh(size_t k, uint64_t h, hash_set const & untrusted) const {
        return m_trusted && m_table.is_single(m_offset + k) && !untrusted.contains(h) && !(m_image && image_name_conflict(h));
    }
    void add_untrusted(size_t count, hash_set & untrusted) const {
        if (!m_trusted)
            for (size_t k = 0; k < count; k++) untrusted.insert(hash(k));
    }
};

// `resolveImportedDuplicate` on the partial map; the map stays exclusive after the call.
uint8 resolve_duplicate(map_builder & b, object * cinfo, object * prev, bool check_error) {
    object * map = b.sync();
    lean_inc(map); lean_inc(cinfo); lean_inc(prev);
    return lean_paperlean_import_resolve_duplicate(map, cinfo, prev, check_error);
}

object * module_constant_names(object * data) { object * n, * c, * e; module_data_arrays(data, &n, &c, &e); return n; }
object * module_constants(object * data) { object * n, * c, * e; module_data_arrays(data, &n, &c, &e); return c; }
object * module_extra_const_names(object * data) { object * n, * c, * e; module_data_arrays(data, &n, &c, &e); return e; }
size_t num_constants(object * data) {
    size_t n = 0;
    if (packed_part_num_constants(data, n)) return n;
    return std::min(lean_array_size(module_constant_names(data)), lean_array_size(module_constants(data)));
}

obj_res mk_some(obj_arg a) {
    object * r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, a);
    return r;
}
obj_res mk_pair(obj_arg a, obj_arg b) {
    object * r = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(r, 0, a);
    lean_ctor_set(r, 1, b);
    return r;
}
}

/*
buildPrivateConstantMaps (moduleData irData : @& Array ModuleData) (privateCapacity c2mCapacity : @& Nat)
  (persistent : Bool) :
  Option (Std.HashMap Name ConstantInfo × Std.HashMap Name ModuleIdx × Option (Nat × Name))

The maps that the fold builds starting from `emptyWithCapacity` of the given capacities, together
with the module index and name of the constant for which the fold calls `throwAlreadyImported`, in
which case the maps are those at that point of the fold; `none` if the capacities are out of range
(the caller then folds). With `persistent`, the new nodes are allocated persistent if all keys and
values are.
*/
extern "C" LEAN_EXPORT obj_res lean_paperlean_build_private_constant_maps(b_obj_arg module_data, b_obj_arg ir_data,
                                                                         b_obj_arg opriv_cap, b_obj_arg oc2m_cap,
                                                                         uint8 persistent) {
    size_t nmods = lean_array_size(module_data);
    size_t nconsts = 0, nextra = 0;
    bool all_persistent = true;
    void const * trusted_pack = image_in_use() ? g_image_packs_trusted : nullptr;
    std::vector<name_source> sources, extra_sources;
    hash_set untrusted;
    for (size_t m = 0; m < nmods; m++) {
        object * data = lean_array_get_core(module_data, m);
        sources.emplace_back(data, module_constant_names(data), false, trusted_pack);
        nconsts += num_constants(data);
        all_persistent = all_persistent && (sources.back().m_packed ||
            (lean_is_persistent(module_constant_names(data)) && lean_is_persistent(module_constants(data))));
        sources.back().add_untrusted(num_constants(data), untrusted);
        if (m < lean_array_size(ir_data)) {
            object * ir = lean_array_get_core(ir_data, m);
            object * extra = module_extra_const_names(ir);
            extra_sources.emplace_back(ir, extra, true, trusted_pack);
            nextra += lean_array_size(extra);
            all_persistent = all_persistent && (extra_sources.back().m_packed || lean_is_persistent(extra));
            extra_sources.back().add_untrusted(lean_array_size(extra), untrusted);
        }
    }
    if (!lean_is_scalar(opriv_cap) || !lean_is_scalar(oc2m_cap) ||
        !map_builder::fits(lean_unbox(opriv_cap), nconsts) || !map_builder::fits(lean_unbox(oc2m_cap), nconsts + nextra))
        return lean_box(0);
    object * priv = mk_empty_map(lean_unbox(opriv_cap));
    object * c2m = mk_empty_map(lean_unbox(oc2m_cap));
    timing_mark("constants.fast.count");
    // Module indices are scalars, so the values of `const2ModIdx` need no counting.
    bool pers = persistent && all_persistent && nmods <= LEAN_MAX_SMALL_NAT;
    map_builder pm(priv, pers, !all_persistent);
    map_builder cm(c2m, pers, !all_persistent || nmods > LEAN_MAX_SMALL_NAT);
    object * err = lean_box(0);
    size_t pb[g_batch], cb[g_batch];
    bool fresh[g_batch];
    for (size_t m = 0; m < nmods && lean_is_scalar(err); m++) {
        object * data = lean_array_get_core(module_data, m);
        object * names = module_constant_names(data);
        object * consts = module_constants(data);
        name_source const & src = sources[m];
        size_t k = num_constants(data);
        object * midx = lean_usize_to_nat(m);
        for (size_t j0 = 0; j0 < k && lean_is_scalar(err); j0 += g_batch) {
            size_t n = std::min(g_batch, k - j0);
            for (size_t t = 0; t < n; t++) {
                uint64_t h = src.hash(j0 + t);
                fresh[t] = src.fresh(j0 + t, h, untrusted);
                pb[t] = pm.bucket(h); pm.prefetch(pb[t]);
                cb[t] = cm.bucket(h); cm.prefetch(cb[t]);
            }
            for (size_t t = 0; t < n; t++) if (!fresh[t]) { pm.prefetch_head(pb[t]); cm.prefetch_head(cb[t]); }
            for (size_t t = 0; t < n; t++) if (!fresh[t]) { pm.prefetch_key(pb[t]); cm.prefetch_key(cb[t]); }
            for (size_t t = 0; t < n; t++) {
                object * name = lean_array_get_core(names, j0 + t);
                object * cinfo = lean_array_get_core(consts, j0 + t);
                if (fresh[t]) {
                    pm.cons(pb[t], name, cinfo);
                    cm.cons(cb[t], name, midx);
                    continue;
                }
                if (object * prev_node = pm.find(pb[t], name)) {
                    uint8 r = resolve_duplicate(pm, cinfo, lean_ctor_get(prev_node, 1), true);
                    if (r == 1) {
                        pm.replace(prev_node, name, cinfo);
                    } else if (r == 2) {
                        lean_inc(name);
                        err = mk_some(mk_pair(lean_usize_to_nat(m), name));
                        break;
                    }
                } else {
                    pm.cons(pb[t], name, cinfo);
                }
                if (!cm.find(cb[t], name))
                    cm.cons(cb[t], name, midx);
            }
        }
        if (lean_is_scalar(err) && m < lean_array_size(ir_data)) {
            object * extra = module_extra_const_names(lean_array_get_core(ir_data, m));
            name_source const & esrc = extra_sources[m];
            for (size_t j = 0; j < lean_array_size(extra); j++) {
                object * name = lean_array_get_core(extra, j);
                uint64_t h = esrc.hash(j);
                size_t i = cm.bucket(h);
                if (esrc.fresh(j, h, untrusted) || !cm.find(i, name))
                    cm.cons(i, name, midx);
            }
        }
        lean_dec(midx);
    }
    timing_mark("constants.fast.build");
    if (!lean_is_scalar(err)) {
        // The import fails; the maps only serve the error message.
        pm.unpersist();
        cm.unpersist();
    } else {
        pm.finish();
        cm.finish();
    }
    return mk_some(mk_pair(pm.sync(), mk_pair(cm.sync(), err)));
}

/*
buildPublicConstantMap (datas : @& Array ModuleData) (capacity : @& Nat) (persistent : Bool) :
  Option (Std.HashMap Name ConstantInfo)

The fold over the public module data of the exported modules, in order.
*/
namespace {
// The public constant map for `buildPublicConstantMap`, or `nullptr` if the capacity is out of range.
// Its nodes are persistent only after `finish` (if `persistent`): until then `discard_map` frees it.
object * build_public_map(b_obj_arg datas, b_obj_arg ocap, bool persistent, bool finish) {
    size_t n = 0;
    bool all_persistent = true;
    void const * trusted_pack = image_in_use() ? g_image_packs_trusted : nullptr;
    std::vector<name_source> sources;
    hash_set untrusted;
    for (size_t m = 0; m < lean_array_size(datas); m++) {
        object * data = lean_array_get_core(datas, m);
        sources.emplace_back(data, module_constant_names(data), false, trusted_pack);
        n += num_constants(data);
        all_persistent = all_persistent && (sources.back().m_packed ||
            (lean_is_persistent(module_constant_names(data)) && lean_is_persistent(module_constants(data))));
        sources.back().add_untrusted(num_constants(data), untrusted);
    }
    if (!lean_is_scalar(ocap) || !map_builder::fits(lean_unbox(ocap), n))
        return nullptr;
    object * pub = mk_empty_map(lean_unbox(ocap));
    map_builder pm(pub, persistent && all_persistent, !all_persistent);
    size_t pb[g_batch];
    bool fresh[g_batch];
    for (size_t m = 0; m < lean_array_size(datas); m++) {
        object * data = lean_array_get_core(datas, m);
        object * names = module_constant_names(data);
        object * consts = module_constants(data);
        name_source const & src = sources[m];
        size_t k = num_constants(data);
        for (size_t j0 = 0; j0 < k; j0 += g_batch) {
            size_t count = std::min(g_batch, k - j0);
            for (size_t t = 0; t < count; t++) {
                uint64_t h = src.hash(j0 + t);
                fresh[t] = src.fresh(j0 + t, h, untrusted);
                pb[t] = pm.bucket(h);
                pm.prefetch(pb[t]);
            }
            for (size_t t = 0; t < count; t++) if (!fresh[t]) pm.prefetch_head(pb[t]);
            for (size_t t = 0; t < count; t++) if (!fresh[t]) pm.prefetch_key(pb[t]);
            for (size_t t = 0; t < count; t++) {
                object * name = lean_array_get_core(names, j0 + t);
                object * cinfo = lean_array_get_core(consts, j0 + t);
                if (fresh[t]) {
                    pm.cons(pb[t], name, cinfo);
                } else if (object * prev_node = pm.find(pb[t], name)) {
                    if (resolve_duplicate(pm, cinfo, lean_ctor_get(prev_node, 1), false) == 1)
                        pm.replace(prev_node, name, cinfo);
                } else {
                    pm.cons(pb[t], name, cinfo);
                }
            }
        }
    }
    if (finish) pm.finish();
    return pm.sync();
}
}

extern "C" LEAN_EXPORT obj_res lean_paperlean_build_public_constant_map(b_obj_arg datas, b_obj_arg ocap, uint8 persistent) {
    object * pub = build_public_map(datas, ocap, persistent, true);
    return pub ? mk_some(pub) : lean_box(0);
}

// =======================================
// Constant maps on several threads
//
// The private constant map, `const2ModIdx` and the public constant map are independent folds over
// the same module data (`const2ModIdx` takes a name if it has no equal key yet, whatever the private
// map does with its constant). When all keys and values are persistent and module indices are
// scalars, building them touches no reference counts of shared objects, so `const2ModIdx` and the
// public map are built on their own threads while the calling thread builds the private map. Each
// map is then exactly what its fold builds. If the private fold fails (`throwAlreadyImported`), the
// maps are dropped and `finalizeImport`'s folds run instead, so that the error and its maps are
// those of the fold.

namespace {
// Whether this process builds the maps on several threads (`PAPERLEAN_IMPORT_THREADS=0`: no).
bool const g_import_threads = [] {
    char const * v = getenv("PAPERLEAN_IMPORT_THREADS");
    return !(v && strcmp(v, "0") == 0);
}();
// Below this many constants, starting threads costs more than it saves.
constexpr size_t g_min_parallel_constants = 16384;

// Frees a map built by `map_builder` before `finish`: each node is referenced once.
void discard_map(object * raw) {
    object * buckets = lean_ctor_get(raw, 1);
    object ** slots = lean_array_cptr(buckets);
    for (size_t i = 0; i < lean_array_size(buckets); i++)
        for (object * n = slots[i]; !lean_is_scalar(n); n = lean_ctor_get(n, 2))
            n->m_rc = 1;
    lean_dec(raw);
}

// A thread that is joined when it goes out of scope.
class joined_thread {
    std::unique_ptr<lthread> m_thread;
public:
    explicit joined_thread(std::function<void()> const & f) : m_thread(new lthread(f)) {}
    void join() { if (m_thread) { m_thread->join(); m_thread.reset(); } }
    ~joined_thread() { try { join(); } catch (...) {} }
};

// `const2ModIdx` alone (persistent nodes, scalar module indices), for the buckets in `[lo, hi)`: the
// names are visited in the order of the fold and each bucket gets its insertions in that order, so
// that threads building disjoint bucket ranges of one map build exactly the fold's map.
void build_c2m_alone(map_builder & cm, b_obj_arg module_data, b_obj_arg ir_data,
                     std::vector<name_source> const & sources, std::vector<name_source> const & extra_sources,
                     hash_set const & untrusted, size_t lo, size_t hi) {
    size_t nmods = lean_array_size(module_data);
    size_t cb[g_batch], idx[g_batch];
    bool fresh[g_batch];
    for (size_t m = 0; m < nmods; m++) {
        object * data = lean_array_get_core(module_data, m);
        object * names = module_constant_names(data);
        name_source const & src = sources[m];
        size_t k = num_constants(data);
        object * midx = lean_box(m);
        for (size_t j0 = 0; j0 < k; j0 += g_batch) {
            size_t n = std::min(g_batch, k - j0);
            size_t c = 0;   // the batch's names in range
            for (size_t t = 0; t < n; t++) {
                uint64_t h = src.hash(j0 + t);
                size_t b = cm.bucket(h);
                if (b < lo || b >= hi) continue;
                idx[c] = j0 + t; cb[c] = b;
                fresh[c] = src.fresh(j0 + t, h, untrusted);
                cm.prefetch(b);
                c++;
            }
            for (size_t t = 0; t < c; t++) if (!fresh[t]) cm.prefetch_head(cb[t]);
            for (size_t t = 0; t < c; t++) if (!fresh[t]) cm.prefetch_key(cb[t]);
            for (size_t t = 0; t < c; t++) {
                object * name = lean_array_get_core(names, idx[t]);
                if (fresh[t] || !cm.find(cb[t], name))
                    cm.cons(cb[t], name, midx);
            }
        }
        if (m < lean_array_size(ir_data)) {
            object * extra = module_extra_const_names(lean_array_get_core(ir_data, m));
            name_source const & esrc = extra_sources[m];
            for (size_t j = 0; j < lean_array_size(extra); j++) {
                uint64_t h = esrc.hash(j);
                size_t i = cm.bucket(h);
                if (i < lo || i >= hi) continue;
                object * name = lean_array_get_core(extra, j);
                if (esrc.fresh(j, h, untrusted) || !cm.find(i, name))
                    cm.cons(i, name, midx);
            }
        }
    }
}

// The private constant map alone; false if the fold fails.
bool build_private_alone(map_builder & pm, b_obj_arg module_data, std::vector<name_source> const & sources,
                         hash_set const & untrusted) {
    size_t nmods = lean_array_size(module_data);
    size_t pb[g_batch];
    bool fresh[g_batch];
    for (size_t m = 0; m < nmods; m++) {
        object * data = lean_array_get_core(module_data, m);
        object * names = module_constant_names(data);
        object * consts = module_constants(data);
        name_source const & src = sources[m];
        size_t k = num_constants(data);
        for (size_t j0 = 0; j0 < k; j0 += g_batch) {
            size_t n = std::min(g_batch, k - j0);
            for (size_t t = 0; t < n; t++) {
                uint64_t h = src.hash(j0 + t);
                fresh[t] = src.fresh(j0 + t, h, untrusted);
                pb[t] = pm.bucket(h); pm.prefetch(pb[t]);
            }
            for (size_t t = 0; t < n; t++) if (!fresh[t]) pm.prefetch_head(pb[t]);
            for (size_t t = 0; t < n; t++) if (!fresh[t]) pm.prefetch_key(pb[t]);
            for (size_t t = 0; t < n; t++) {
                object * name = lean_array_get_core(names, j0 + t);
                object * cinfo = lean_array_get_core(consts, j0 + t);
                if (fresh[t]) {
                    pm.cons(pb[t], name, cinfo);
                } else if (object * prev_node = pm.find(pb[t], name)) {
                    uint8 r = resolve_duplicate(pm, cinfo, lean_ctor_get(prev_node, 1), true);
                    if (r == 1)
                        pm.replace(prev_node, name, cinfo);
                    else if (r == 2)
                        return false;
                } else {
                    pm.cons(pb[t], name, cinfo);
                }
            }
        }
    }
    return true;
}

bool arrays_persistent(b_obj_arg datas) {
    for (size_t m = 0; m < lean_array_size(datas); m++) {
        object * data = lean_array_get_core(datas, m);
        if (!lean_is_persistent(module_constant_names(data)) || !lean_is_persistent(module_constants(data)))
            return false;
    }
    return true;
}
}

/*
buildConstantMaps (moduleData irData publicDatas : @& Array ModuleData)
  (privateCapacity c2mCapacity publicCapacity : @& Nat) (persistent buildPublic : Bool) :
  Option (Std.HashMap Name ConstantInfo × Std.HashMap Name ModuleIdx × Option (Nat × Name)) ×
    Option (Std.HashMap Name ConstantInfo)

`buildPrivateConstantMaps` and, with `buildPublic`, `buildPublicConstantMap` of `publicDatas`, built
concurrently where that is possible. The public map is `none` if it was not built here (the caller
builds it then). Both are `none` if the private fold fails on the concurrent path (the caller folds).
*/
extern "C" LEAN_EXPORT obj_res lean_paperlean_build_constant_maps(b_obj_arg module_data, b_obj_arg ir_data,
                                                                 b_obj_arg public_datas, b_obj_arg opriv_cap,
                                                                 b_obj_arg oc2m_cap, b_obj_arg opub_cap,
                                                                 uint8 persistent, uint8 build_public) {
    size_t nmods = lean_array_size(module_data);
    size_t nconsts = 0, nextra = 0;
    for (size_t m = 0; m < nmods; m++) {
        nconsts += num_constants(lean_array_get_core(module_data, m));
        if (m < lean_array_size(ir_data))
            nextra += lean_array_size(module_extra_const_names(lean_array_get_core(ir_data, m)));
    }
    bool parallel = g_import_threads && persistent && nmods <= LEAN_MAX_SMALL_NAT &&
        nconsts >= g_min_parallel_constants && lean_is_scalar(opriv_cap) && lean_is_scalar(oc2m_cap) &&
        map_builder::fits(lean_unbox(opriv_cap), nconsts) && map_builder::fits(lean_unbox(oc2m_cap), nconsts + nextra) &&
        arrays_persistent(module_data);
    for (size_t m = 0; parallel && m < std::min(nmods, lean_array_size(ir_data)); m++)
        parallel = lean_is_persistent(module_extra_const_names(lean_array_get_core(ir_data, m)));
#if !defined(LEAN_MULTI_THREAD)
    parallel = false;
#endif
    if (!parallel) {
        object * priv = lean_paperlean_build_private_constant_maps(module_data, ir_data, opriv_cap, oc2m_cap, persistent);
        return mk_pair(priv, lean_box(0));
    }
    // Every key and value is persistent, so new nodes are persistent and nothing is counted.
    void const * trusted_pack = image_in_use() ? g_image_packs_trusted : nullptr;
    std::vector<name_source> sources, extra_sources;
    hash_set untrusted;
    for (size_t m = 0; m < nmods; m++) {
        object * data = lean_array_get_core(module_data, m);
        sources.emplace_back(data, module_constant_names(data), false, trusted_pack);
        sources.back().add_untrusted(num_constants(data), untrusted);
        if (m < lean_array_size(ir_data)) {
            object * ir = lean_array_get_core(ir_data, m);
            extra_sources.emplace_back(ir, module_extra_const_names(ir), true, trusted_pack);
            extra_sources.back().add_untrusted(lean_array_size(module_extra_const_names(ir)), untrusted);
        }
    }
    timing_mark("constants.fast.sources");
    bool public_here = build_public && arrays_persistent(public_datas);
    object * pub = nullptr;
    object * c2m = nullptr;
    size_t c2m_cap = lean_unbox(oc2m_cap);
    // (with `PAPERLEAN_IMPORT_TIMING`, the helpers' own durations in ms: c2m halves, public)
    double t_c2m[2] = { 0, 0 }, t_pub = 0;
    size_t c2m_count[2] = { 0, 0 };
    auto ms_since = [](std::chrono::steady_clock::time_point t0) {
        return std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - t0).count();
    };
    // `const2ModIdx` is built by two threads, each for half of its buckets
    c2m = mk_empty_map(c2m_cap);
    size_t c2m_buckets = map_builder(c2m, true, false).num_buckets();
    std::unique_ptr<joined_thread> pub_thread, c2m_thread[2];
    try {
        if (public_here)
            pub_thread.reset(new joined_thread([&] {
                auto t0 = std::chrono::steady_clock::now();
                pub = build_public_map(public_datas, opub_cap, true, false);
                t_pub = ms_since(t0);
            }));
        for (int half = 0; half < 2; half++)
            c2m_thread[half].reset(new joined_thread([&, half] {
                auto t0 = std::chrono::steady_clock::now();
                map_builder cm(c2m, true, false);
                size_t mid = c2m_buckets / 2;
                build_c2m_alone(cm, module_data, ir_data, sources, extra_sources, untrusted,
                                half == 0 ? 0 : mid, half == 0 ? mid : c2m_buckets);
                c2m_count[half] = cm.count();
                t_c2m[half] = ms_since(t0);
            }));
    } catch (...) {
        // no threads: build them one after the other
        for (auto & t : c2m_thread) if (t) t->join();
        if (pub_thread) pub_thread->join();
        if (pub) discard_map(pub);
        discard_map(c2m);
        object * priv = lean_paperlean_build_private_constant_maps(module_data, ir_data, opriv_cap, oc2m_cap, persistent);
        return mk_pair(priv, lean_box(0));
    }
    object * priv = mk_empty_map(lean_unbox(opriv_cap));
    timing_mark("constants.fast.count");
    map_builder pm(priv, true, false);
    bool ok = build_private_alone(pm, module_data, sources, untrusted);
    pm.sync();
    timing_mark("constants.fast.build");
    for (auto & t : c2m_thread) t->join();
    if (pub_thread) pub_thread->join();
    timing_mark("constants.fast.join");
    {
        map_builder cm(c2m, true, false);
        cm.set_count(c2m_count[0] + c2m_count[1]);
        cm.sync();
    }
    if (import_timing_enabled())
        fprintf(stderr, "paperlean-counter constants.threads c2m_lo=%.3f c2m_hi=%.3f public=%.3f\n",
                t_c2m[0], t_c2m[1], t_pub);
    if (!ok) {
        discard_map(priv);
        discard_map(c2m);
        if (pub) discard_map(pub);
        return mk_pair(lean_box(0), lean_box(0));
    }
    map_builder(priv, true, false).finish();
    map_builder(c2m, true, false).finish();
    if (pub) map_builder(pub, true, false).finish();
    return mk_pair(mk_some(mk_pair(priv, mk_pair(c2m, lean_box(0)))), pub ? mk_some(pub) : lean_box(0));
}
}
