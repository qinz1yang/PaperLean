/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include <algorithm>
#include <vector>
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
// `PAPERLEAN_HEARTBEATS=lean`: no optimization that lowers heartbeat counts while elaborating
bool g_lean_heartbeats = [] {
    char const * h = getenv("PAPERLEAN_HEARTBEATS");
    return h && strcmp(h, "lean") == 0;
}();

struct timing_point { double wall_ms, cpu_ms; long minflt; };
timing_point timing_now() {
#ifdef LEAN_WINDOWS
    // wall time only
    double ms = std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now().time_since_epoch()).count();
    return { ms, ms, 0 };
#else
    timespec w, c;
    clock_gettime(CLOCK_MONOTONIC, &w);
    clock_gettime(CLOCK_THREAD_CPUTIME_ID, &c);
    rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    return { w.tv_sec * 1e3 + w.tv_nsec / 1e6, c.tv_sec * 1e3 + c.tv_nsec / 1e6, ru.ru_minflt };
#endif
}
bool g_import_timing = getenv("PAPERLEAN_IMPORT_TIMING") != nullptr;
timing_point g_last_timing = timing_now();
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

bool lean_heartbeats_mode() { return g_lean_heartbeats; }

void import_timing_add(import_counter c, uint64_t ns) {
    g_counter_ns[c] += ns;
    g_counter_calls[c]++;
}

/* uncountedHeartbeats {α} (act : IO α) : IO α */
extern "C" LEAN_EXPORT obj_res lean_paperlean_uncounted_heartbeats(obj_arg act) {
    uncounted_heartbeats uncounted;
    return apply_1(act, io_mk_world());
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

// The names one module data contributes: their hashes come from its pack's name table if the table
// is trusted, which holds for the parts of a single pack, the first one met. A name of a trusted
// table that `is_single` in it can only have an equal key in the map if some untrusted name has its
// hash; the hashes of all untrusted names are collected beforehand.
struct name_source {
    object * m_names;
    part_names m_table;
    bool m_trusted = false;
    bool m_packed = false;
    size_t m_offset = 0;    // index of `m_names[0]` in the table
    name_source(object * data, object * names, bool extra, void const *& trusted_pack) : m_names(names) {
        m_packed = packed_part_names(data, m_table);
        if (m_packed && m_table.hashes && (!trusted_pack || trusted_pack == m_table.pack)) {
            trusted_pack = m_table.pack;
            m_trusted = true;
            m_offset = extra ? m_table.num_const_names : 0;
        }
    }
    uint64_t hash(size_t k) const {
        return m_trusted ? m_table.hashes[m_offset + k] : lean_name_hash(lean_array_get_core(m_names, k));
    }
    // Whether name `k`, of hash `h`, cannot have an equal key in the map.
    bool fresh(size_t k, uint64_t h, hash_set const & untrusted) const {
        return m_trusted && m_table.is_single(m_offset + k) && !untrusted.contains(h);
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
    void const * trusted_pack = nullptr;
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
extern "C" LEAN_EXPORT obj_res lean_paperlean_build_public_constant_map(b_obj_arg datas, b_obj_arg ocap, uint8 persistent) {
    size_t n = 0;
    bool all_persistent = true;
    void const * trusted_pack = nullptr;
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
        return lean_box(0);
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
    pm.finish();
    return mk_some(pm.sync());
}
}

/*
A sampling profiler for development: with `PAPERLEAN_PROFILE=<file>`, the process records the
program counter and the call stack every millisecond of its CPU time (user and system, so that time
in page faults and system calls is charged to the instruction that caused it), and writes the
samples and its memory map to `<file>.<pid>` at exit. The samples are symbolized offline.
*/
#if defined(__linux__) && defined(__x86_64__)
#include <algorithm>
#include <atomic>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <csignal>
#include <csetjmp>
#include <ucontext.h>
#include <unwind.h>
#include <sys/time.h>
#include <unistd.h>

namespace {
// Each sample: the interrupted program counter, then the return addresses found by unwinding from the
// signal handler (which include the handler's own frames), 0-terminated.
constexpr size_t g_sample_words = 128;
constexpr size_t g_max_samples = 1 << 17;
uintptr_t * g_samples = nullptr;
std::atomic<size_t> g_num_samples{0};
char const * g_out = nullptr;

struct backtrace_state { uintptr_t * out; size_t n, max; };

_Unwind_Reason_Code on_frame(_Unwind_Context * ctx, void * arg) {
    backtrace_state * s = static_cast<backtrace_state *>(arg);
    if (s->n >= s->max) return _URC_END_OF_STACK;
    s->out[s->n++] = _Unwind_GetIP(ctx);
    return _URC_NO_REASON;
}

// The unwinder can fault on frames whose unwind information does not describe every instruction.
// Such a fault happens after it has looked up the frame's information (and released its locks), so
// the sample is dropped by jumping back out of the handler; other faults go to the previous handler
// (Lean's stack overflow detection).
__thread __attribute__((tls_model("initial-exec"))) bool g_in_sample = false;
__thread __attribute__((tls_model("initial-exec"))) sigjmp_buf g_sample_jmp;
struct sigaction g_prev_segv, g_prev_bus;

void on_fault(int sig, siginfo_t * info, void * ctx) {
    if (g_in_sample) siglongjmp(g_sample_jmp, 1);
    struct sigaction & prev = sig == SIGSEGV ? g_prev_segv : g_prev_bus;
    if (prev.sa_flags & SA_SIGINFO) {
        if (prev.sa_sigaction) { prev.sa_sigaction(sig, info, ctx); return; }
    } else if (prev.sa_handler != SIG_DFL && prev.sa_handler != SIG_IGN) {
        prev.sa_handler(sig);
        return;
    }
    // the default action: let the faulting instruction fault again without this handler
    sigaction(sig, &prev, nullptr);
}

// (Re)installs `on_fault`, which Lean's initialization may have replaced, remembering the handler it
// replaces.
void install_fault_handler(int sig, struct sigaction & prev) {
    struct sigaction cur;
    if (sigaction(sig, nullptr, &cur) != 0 || ((cur.sa_flags & SA_SIGINFO) && cur.sa_sigaction == on_fault)) return;
    struct sigaction sa = {};
    sa.sa_sigaction = on_fault;
    sa.sa_flags = SA_SIGINFO | SA_ONSTACK | SA_NODEFER;
    sigemptyset(&sa.sa_mask);
    prev = cur;
    sigaction(sig, &sa, nullptr);
}

void on_sample(int, siginfo_t *, void * ctx) {
    install_fault_handler(SIGSEGV, g_prev_segv);
    install_fault_handler(SIGBUS, g_prev_bus);
    size_t i = g_num_samples.fetch_add(1, std::memory_order_relaxed);
    if (i >= g_max_samples) return;
    uintptr_t * out = g_samples + i * g_sample_words;
    out[0] = static_cast<uintptr_t>(static_cast<ucontext_t *>(ctx)->uc_mcontext.gregs[REG_RIP]);
    out[1] = 0;
    if (sigsetjmp(g_sample_jmp, 1) != 0) {
        // the unwinder faulted: keep the program counter only
        g_in_sample = false;
        out[1] = 0;
        return;
    }
    g_in_sample = true;
    backtrace_state s { out + 1, 0, g_sample_words - 2 };
    _Unwind_Backtrace(on_frame, &s);
    out[1 + s.n] = 0;
    g_in_sample = false;
}

void write_samples() {
    itimerval stop = {};
    setitimer(ITIMER_PROF, &stop, nullptr);
    char path[4096];
    snprintf(path, sizeof(path), "%s.%d", g_out, static_cast<int>(getpid()));
    FILE * f = fopen(path, "w");
    if (!f) return;
    if (FILE * maps = fopen("/proc/self/maps", "r")) {
        char line[4096];
        while (fgets(line, sizeof(line), maps)) fprintf(f, "map %s", line);
        fclose(maps);
    }
    size_t n = std::min(g_num_samples.load(), g_max_samples);
    for (size_t i = 0; i < n; i++) {
        uintptr_t * sample = g_samples + i * g_sample_words;
        fprintf(f, "pc %lx", static_cast<unsigned long>(sample[0]));
        for (size_t j = 1; j < g_sample_words && sample[j]; j++) fprintf(f, " %lx", static_cast<unsigned long>(sample[j]));
        fprintf(f, "\n");
    }
    fclose(f);
}

struct sample_profiler {
    sample_profiler() {
        g_out = getenv("PAPERLEAN_PROFILE");
        if (!g_out || !*g_out) return;
        g_samples = static_cast<uintptr_t *>(calloc(g_max_samples * g_sample_words, sizeof(uintptr_t)));
        if (!g_samples) return;
        struct sigaction sa = {};
        sa.sa_sigaction = on_sample;
        sa.sa_flags = SA_SIGINFO | SA_RESTART;
        sigemptyset(&sa.sa_mask);
        sigaction(SIGPROF, &sa, nullptr);
        itimerval t = {};
        t.it_interval.tv_usec = 1000;
        t.it_value.tv_usec = 1000;
        setitimer(ITIMER_PROF, &t, nullptr);
        atexit(write_samples);
    }
} g_sample_profiler;
}
#endif
