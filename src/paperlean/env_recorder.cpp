/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include <atomic>
#include <cstring>
#include <vector>
#include "runtime/object.h"

// Part of the runtime (`src/runtime/CMakeLists.txt`), as tasks report to it.
// The recorder of environment accesses of `Lean.PaperLean.EnvDeps`: while a thread records, the
// hooks in `Lean.Environment` and elsewhere pass it every access to the environment, as an access and
// a check of whether another environment gives the same answer, or mark the recording as unusable.

namespace lean {
struct env_recorder {
    std::vector<object *> m_accesses;
    std::vector<object *> m_checks;
    // why the recording is unusable, if it is
    char const * m_unusable = nullptr;
};

// the number of threads recording, so that other threads do not read their thread-local slot
static std::atomic<unsigned> g_env_recorders{0};
static thread_local std::vector<env_recorder *> * t_env_recorders = nullptr;

// (a null entry pauses the recording below it, `envWithoutRecording`)
static env_recorder * current_env_recorder() {
    if (g_env_recorders.load(std::memory_order_relaxed) == 0) return nullptr;
    if (!t_env_recorders || t_env_recorders->empty()) return nullptr;
    return t_env_recorders->back();
}

/* withoutRecording (f : Unit → α) : α */
extern "C" LEAN_EXPORT obj_res lean_paperlean_env_without_recording(obj_arg f) {
    if (!current_env_recorder()) return lean_apply_1(f, lean_box(0));
    struct pause {
        pause() { t_env_recorders->push_back(nullptr); }
        ~pause() { t_env_recorders->pop_back(); }
    } p;
    return lean_apply_1(f, lean_box(0));
}

/* pause : BaseIO Bool -- pauses this thread's recording, if it records, and returns whether it did */
extern "C" LEAN_EXPORT uint8 lean_paperlean_env_pause() {
    if (!current_env_recorder()) return false;
    t_env_recorders->push_back(nullptr);
    return true;
}

/* resume (paused : Bool) : BaseIO Unit -- ends the pause of `pause` if it paused */
extern "C" LEAN_EXPORT obj_res lean_paperlean_env_resume(uint8 paused) {
    if (paused) t_env_recorders->pop_back();
    return box(0);
}

/* recording (dummy : @& α) : Bool -- whether this thread records */
extern "C" LEAN_EXPORT uint8 lean_paperlean_env_recording(b_obj_arg) {
    return current_env_recorder() != nullptr;
}

/* record (access check : NonScalar) (r : α) : α -- records `access` and its `check`, returns `r` */
extern "C" LEAN_EXPORT obj_res lean_paperlean_env_record(obj_arg access, obj_arg check, obj_arg r) {
    if (env_recorder * rec = current_env_recorder()) {
        rec->m_accesses.push_back(access);
        rec->m_checks.push_back(check);
    } else {
        lean_dec(access);
        lean_dec(check);
    }
    return r;
}

static void mark_unusable(char const * why) {
    if (env_recorder * rec = current_env_recorder())
        if (!rec->m_unusable) rec->m_unusable = why;
}

/* markUnusable (why : @& String) (r : α) : α -- the recording cannot be checked (e.g. the whole
   constant map was read); `why` must be a literal (it is kept without a reference) */
extern "C" LEAN_EXPORT obj_res lean_paperlean_env_mark_unusable(b_obj_arg why, obj_arg r) {
    mark_unusable(lean_string_cstr(why));
    return r;
}

/* markUnusableIO (why : @& String) : BaseIO Unit (`BaseIO` functions take no world and return their
   value); as `markUnusable`, but `why` is copied */
extern "C" LEAN_EXPORT obj_res lean_paperlean_env_mark_unusable_io(b_obj_arg why) {
    if (env_recorder * rec = current_env_recorder())
        if (!rec->m_unusable) rec->m_unusable = strdup(lean_string_cstr(why));
    return box(0);
}

/* Called when a task is created: work of a recording thread done by another thread is not recorded. */
extern "C" LEAN_EXPORT void lean_paperlean_env_note_task() {
    mark_unusable("a task");
}

/* recordAll (accesses : @& Array EnvAccess) (checks : @& Array NonScalar) : BaseIO Unit -- records the
   accesses of an earlier recording, e.g. of a result reused within this one */
extern "C" LEAN_EXPORT obj_res lean_paperlean_env_record_all(b_obj_arg accesses, b_obj_arg checks) {
    if (env_recorder * rec = current_env_recorder()) {
        size_t n = lean_array_size(accesses);
        for (size_t i = 0; i < n; i++) {
            object * a = lean_array_get_core(accesses, i);
            object * c = lean_array_get_core(checks, i);
            lean_inc(a);
            lean_inc(c);
            rec->m_accesses.push_back(a);
            rec->m_checks.push_back(c);
        }
    }
    return box(0);
}

/* start : BaseIO Unit */
extern "C" LEAN_EXPORT obj_res lean_paperlean_env_start_recording() {
    if (!t_env_recorders) t_env_recorders = new std::vector<env_recorder *>();
    t_env_recorders->push_back(new env_recorder());
    g_env_recorders.fetch_add(1, std::memory_order_relaxed);
    return box(0);
}

/* stop : BaseIO (Array NonScalar × Array NonScalar × String) -- the accesses, their checks, and why
   the recording is unusable (empty if it is usable); ends the recording started last on this thread */
extern "C" LEAN_EXPORT obj_res lean_paperlean_env_stop_recording() {
    lean_assert(t_env_recorders && !t_env_recorders->empty());
    env_recorder * rec = t_env_recorders->back();
    t_env_recorders->pop_back();
    g_env_recorders.fetch_sub(1, std::memory_order_relaxed);
    // a recording that this one was nested in (and that is not paused) depends on everything this
    // one read
    if (!t_env_recorders->empty()) {
        if (env_recorder * below = t_env_recorders->back()) {
            for (size_t i = 0; i < rec->m_accesses.size(); i++) {
                lean_inc(rec->m_accesses[i]);
                lean_inc(rec->m_checks[i]);
                below->m_accesses.push_back(rec->m_accesses[i]);
                below->m_checks.push_back(rec->m_checks[i]);
            }
            if (rec->m_unusable && !below->m_unusable) below->m_unusable = rec->m_unusable;
        }
    }
    object * accesses = lean_alloc_array(rec->m_accesses.size(), rec->m_accesses.size());
    object * checks = lean_alloc_array(rec->m_checks.size(), rec->m_checks.size());
    for (size_t i = 0; i < rec->m_accesses.size(); i++) {
        lean_array_set_core(accesses, i, rec->m_accesses[i]);
        lean_array_set_core(checks, i, rec->m_checks[i]);
    }
    object * why = lean_mk_string(rec->m_unusable ? rec->m_unusable : "");
    delete rec;
    object * inner = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(inner, 0, checks);
    lean_ctor_set(inner, 1, why);
    object * outer = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(outer, 0, accesses);
    lean_ctor_set(outer, 1, inner);
    return outer;
}
}
