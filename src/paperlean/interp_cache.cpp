/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include <mutex>
#include <shared_mutex>
#include <vector>
#include "runtime/object.h"
#include "util/name.h"
#include "util/name_hash_map.h"
#include "paperlean/fast_import.h"
#include "paperlean/interp_cache.h"

namespace lean {
// `Lean.PaperLean.Import`; the arguments are owned
extern "C" obj_res lean_paperlean_env_imports_id(obj_arg env);
extern "C" uint8 lean_paperlean_is_imported_const(obj_arg env, obj_arg n);

namespace {
std::shared_mutex g_shared_symbols_mutex;
// per import (`lean_paperlean_env_imports_id`, persistent), the shared entries; a process imports a
// few times at most
std::vector<std::pair<object *, name_hash_map<shared_symbol>>> * g_shared_symbols =
    new std::vector<std::pair<object *, name_hash_map<shared_symbol>>>();

// The persistent object that identifies the imports of `env`, or `nullptr`.
object * persistent_imports(b_obj_arg env) {
    lean_inc(env);
    object * h = lean_paperlean_env_imports_id(env);
    bool persistent = !lean_is_scalar(h) && lean_is_persistent(h);
    lean_dec(h);
    return persistent ? h : nullptr;
}
}

bool find_shared_symbol(b_obj_arg env, b_obj_arg fn, shared_symbol & s) {
    if (import_legacy_mode() || lean_heartbeats_mode()) return false;
    uncounted_heartbeats uncounted;
    object * h = persistent_imports(env);
    if (!h) return false;
    std::shared_lock<std::shared_mutex> lock(g_shared_symbols_mutex);
    for (auto const & e : *g_shared_symbols) {
        if (e.first != h) continue;
        auto it = e.second.find(name(fn, true));
        if (it == e.second.end()) return false;
        s = it->second;
        return true;
    }
    return false;
}

void share_symbol(b_obj_arg env, b_obj_arg fn, shared_symbol const & s) {
    // the entry is used on any thread, so its declaration must not be reference counted
    if (import_legacy_mode() || lean_heartbeats_mode() || lean_is_scalar(s.decl) || !lean_is_persistent(s.decl)) return;
    uncounted_heartbeats uncounted;
    object * h = persistent_imports(env);
    if (!h) return;
    lean_inc(env); lean_inc(fn);
    if (!lean_paperlean_is_imported_const(env, fn)) return;
    std::unique_lock<std::shared_mutex> lock(g_shared_symbols_mutex);
    for (auto & e : *g_shared_symbols) {
        if (e.first != h) continue;
        e.second.insert({ name(fn, true), s });
        return;
    }
    g_shared_symbols->emplace_back(h, name_hash_map<shared_symbol>());
    g_shared_symbols->back().second.insert({ name(fn, true), s });
}
}
