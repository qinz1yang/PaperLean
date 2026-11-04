/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include <atomic>
#include <cstdio>
#include <cstdlib>
#include "runtime/object.h"

// The mark of the threads that elaborate commands in order, the frontend of the process that reuses,
// what reuse keeps, and the end of a run whose oracle found a difference, for
// `Lean.PaperLean.Speculation`. Printed with the C stream: Lean's streams of a thread may be held by
// `IO.FS.withIsolatedStreams`, whose contents this process does not get to print.

namespace lean {
static thread_local bool t_elab_thread = false;

// Which frontend of the process reuses: the first, if the command-line `lean` runs it, and no other,
// as the stores below need a single user.
enum : uint8_t { no_frontend, command_line, reusing, off };
static std::atomic<uint8_t> g_reuse_state{no_frontend};

/* setElabThread (on : Bool) : BaseIO Unit */
extern "C" LEAN_EXPORT obj_res lean_paperlean_set_elab_thread(uint8 on) {
    t_elab_thread = on;
    return box(0);
}

/* noteCommandLine : BaseIO Unit */
extern "C" LEAN_EXPORT obj_res lean_paperlean_note_command_line() {
    uint8_t s = no_frontend;
    g_reuse_state.compare_exchange_strong(s, command_line);
    return box(0);
}

/* onElabThread : BaseIO Bool */
extern "C" LEAN_EXPORT uint8 lean_paperlean_elab_thread() {
    return t_elab_thread && g_reuse_state.load(std::memory_order_relaxed) == reusing;
}

/* noteFrontendCore (fileName : @& String) : BaseIO Unit */
extern "C" LEAN_EXPORT obj_res lean_paperlean_note_frontend(b_obj_arg file_name) {
    uint8_t s = command_line;
    if (!g_reuse_state.compare_exchange_strong(s, reusing) && g_reuse_state.exchange(off) == reusing) {
        std::fprintf(stderr, "PaperLean: a further frontend in this process (%s): reuse of results and "
                     "its oracle are off from here on\n", lean_string_cstr(file_name));
    }
    return box(0);
}

// The number of searches and elaborations left out of reuse in each way, from any thread.
static constexpr unsigned g_num_exclusions = 16;
static std::atomic<uint64_t> g_exclusions[g_num_exclusions];

/* noteExclusionCore (kind : UInt8) : BaseIO Bool -- whether it is the first of its kind */
extern "C" LEAN_EXPORT uint8 lean_paperlean_note_exclusion(uint8 kind) {
    return g_exclusions[kind % g_num_exclusions].fetch_add(1, std::memory_order_relaxed) == 0;
}

/* exclusionCount (kind : UInt8) : BaseIO Nat */
extern "C" LEAN_EXPORT obj_res lean_paperlean_exclusions(uint8 kind) {
    return lean_uint64_to_nat(g_exclusions[kind % g_num_exclusions].load(std::memory_order_relaxed));
}

// What reuse keeps, by slot (`Lean.PaperLean.TCCache.takeEntries` 0,
// `Lean.PaperLean.SectionVars.takeEntries` 1), whose objects are not marked multi-threaded: only the
// threads where `onElabThread` holds use it, one at a time (`Lean.PaperLean.TCCache.getEntries?`). A
// slot holds `box(0)` until something is put there, and `nullptr` while it is taken: a thread that
// finds it taken, which would be a defect, turns reuse off.
static std::atomic<object *> g_stores[2] = {{box(0)}, {box(0)}};

static void note_store_conflict() {
    if (g_reuse_state.exchange(off) == reusing) {
        std::fprintf(stderr, "PaperLean: two threads use what reuse keeps at once: reuse of results and "
                     "its oracle are off from here on\n");
    }
}

/* takeEntries (slot : UInt8) (empty : α) : BaseIO (Option α) */
extern "C" LEAN_EXPORT obj_res lean_paperlean_take_store(uint8 slot, obj_arg empty) {
    object * m = g_stores[slot % 2].exchange(nullptr, std::memory_order_acquire);
    if (m == nullptr) {
        note_store_conflict();
        dec(empty);
        return box(0);
    }
    if (lean_is_scalar(m))
        m = empty;
    else
        dec(empty);
    object * r = alloc_cnstr(1, 1, 0);
    cnstr_set(r, 0, m);
    return r;
}

/* putEntries (slot : UInt8) (m : α) : BaseIO Unit */
extern "C" LEAN_EXPORT obj_res lean_paperlean_put_store(uint8 slot, obj_arg m) {
    // A conflicting owner disables reuse; its displaced object may still be in use.
    if (g_stores[slot % 2].exchange(m, std::memory_order_release) != nullptr)
        note_store_conflict();
    return box(0);
}

/* fail (reason : @& String) : BaseIO Unit -- does not return */
extern "C" LEAN_EXPORT obj_res lean_paperlean_speculation_fail(b_obj_arg reason) {
    std::fflush(stdout);
    std::fprintf(stderr, "PaperLean: the reuse oracle found a difference: %s\n", lean_string_cstr(reason));
    std::fflush(stderr);
    std::_Exit(EXIT_FAILURE);
}
}
