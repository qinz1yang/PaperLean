/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include <atomic>
#include <memory>
#include <mutex>
#include "runtime/object.h"
#include "paperlean/fast_import.h"
#include "paperlean/interp_cache.h"

namespace lean {
// `Lean.PaperLean.Import`; the arguments are owned
extern "C" obj_res lean_paperlean_env_imports_id(obj_arg env);
extern "C" uint8 lean_paperlean_is_imported_const(obj_arg env, obj_arg n);

namespace {
struct shared_entry {
    object * fn;    // a reference that is never released
    shared_symbol s;
};

// The shared entries of an import, which interpreters on all threads look up: an insert-only open
// addressing table that they read without a lock (a mutex, even a shared one, makes them wait for
// each other). A slot, once set, never changes; a table that fills up is replaced by a larger one,
// and the old one stays, as a reader may still be in it: it may then not find an entry, and looks
// the symbol up itself, which finds the same.
struct shared_table {
    size_t mask;
    size_t count = 0;   // (writers only)
    std::unique_ptr<std::atomic<shared_entry *>[]> slots;
    explicit shared_table(size_t capacity) : mask(capacity - 1), slots(new std::atomic<shared_entry *>[capacity]) {
        for (size_t i = 0; i < capacity; i++) slots[i].store(nullptr, std::memory_order_relaxed);
    }
};

// per import (`lean_paperlean_env_imports_id`, persistent), its table; a process imports a few times
// at most, and the imports beyond these share nothing
constexpr size_t g_max_imports = 8;
std::atomic<object *> g_keys[g_max_imports] = {};
std::atomic<shared_table *> g_tables[g_max_imports] = {};
std::mutex g_writer_mutex;

shared_entry * find_in(shared_table const & t, object * fn) {
    for (size_t i = lean_name_hash(fn) & t.mask;; i = (i + 1) & t.mask) {
        shared_entry * e = t.slots[i].load(std::memory_order_acquire);
        // (at most half of the slots are set)
        if (!e) return nullptr;
        if (e->fn == fn || lean_name_eq(e->fn, fn)) return e;
    }
}

// (with `g_writer_mutex`)
void insert_into(shared_table & t, shared_entry * e) {
    size_t i = lean_name_hash(e->fn) & t.mask;
    while (t.slots[i].load(std::memory_order_relaxed)) i = (i + 1) & t.mask;
    t.slots[i].store(e, std::memory_order_release);
    t.count++;
}
}

object * shared_symbols_key(b_obj_arg env) {
    if (import_legacy_mode()) return nullptr;
    uncounted_heartbeats uncounted;
    lean_inc(env);
    object * h = lean_paperlean_env_imports_id(env);
    bool persistent = !lean_is_scalar(h) && lean_is_persistent(h);
    lean_dec(h);
    return persistent ? h : nullptr;
}

bool find_shared_symbol(object * key, b_obj_arg fn, shared_symbol & s) {
    if (!key) return false;
    for (size_t k = 0; k < g_max_imports; k++) {
        object * other = g_keys[k].load(std::memory_order_acquire);
        if (!other) return false;
        if (other != key) continue;
        shared_entry * e = find_in(*g_tables[k].load(std::memory_order_acquire), fn);
        if (!e) return false;
        s = e->s;
        return true;
    }
    return false;
}

void share_symbol(object * key, b_obj_arg env, b_obj_arg fn, shared_symbol const & s) {
    // the entry is used on any thread, so its declaration must not be reference counted
    if (!key || lean_is_scalar(s.decl) || !lean_is_persistent(s.decl)) return;
    uncounted_heartbeats uncounted;
    lean_inc(env); lean_inc(fn);
    if (!lean_paperlean_is_imported_const(env, fn)) return;
    std::lock_guard<std::mutex> lock(g_writer_mutex);
    size_t k = 0;
    while (k < g_max_imports && g_keys[k].load(std::memory_order_relaxed) &&
           g_keys[k].load(std::memory_order_relaxed) != key)
        k++;
    if (k == g_max_imports) return;
    shared_table * t = g_tables[k].load(std::memory_order_relaxed);
    if (!t) {
        t = new shared_table(4096);
        // (the table first, which a reader that finds the key reads)
        g_tables[k].store(t, std::memory_order_release);
        g_keys[k].store(key, std::memory_order_release);
    }
    if (find_in(*t, fn)) return;
    if (2 * (t->count + 1) > t->mask + 1) {
        shared_table * larger = new shared_table(2 * (t->mask + 1));
        for (size_t i = 0; i <= t->mask; i++)
            if (shared_entry * e = t->slots[i].load(std::memory_order_relaxed)) insert_into(*larger, e);
        g_tables[k].store(larger, std::memory_order_release);
        t = larger;
    }
    lean_inc(fn);
    insert_into(*t, new shared_entry { fn, s });
}
}
