/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include <atomic>
#include <cstdio>
#include <cstdlib>
#include "runtime/object.h"

// The mark of the threads that elaborate commands in order, the end of reuse in a process with more
// than one frontend, and the end of a run whose oracle found a difference, for
// `Lean.PaperLean.Speculation`. Printed with the C stream: Lean's streams of a thread may be held by
// `IO.FS.withIsolatedStreams`, whose contents this process does not get to print.

namespace lean {
static thread_local bool t_elab_thread = false;
static std::atomic<bool> g_frontend_seen{false};
static std::atomic<bool> g_reuse_off{false};

/* setElabThread (on : Bool) : BaseIO Unit */
extern "C" LEAN_EXPORT obj_res lean_paperlean_set_elab_thread(uint8 on) {
    t_elab_thread = on;
    return box(0);
}

/* onElabThread : BaseIO Bool */
extern "C" LEAN_EXPORT uint8 lean_paperlean_elab_thread() {
    return t_elab_thread && !g_reuse_off.load(std::memory_order_relaxed);
}

/* noteFrontendCore (fileName : @& String) : BaseIO Unit */
extern "C" LEAN_EXPORT obj_res lean_paperlean_note_frontend(b_obj_arg file_name) {
    if (g_frontend_seen.exchange(true) && !g_reuse_off.exchange(true)) {
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

/* fail (reason : @& String) : BaseIO Unit -- does not return */
extern "C" LEAN_EXPORT obj_res lean_paperlean_speculation_fail(b_obj_arg reason) {
    std::fflush(stdout);
    std::fprintf(stderr, "PaperLean: the reuse oracle found a difference: %s\n", lean_string_cstr(reason));
    std::fflush(stderr);
    std::_Exit(EXIT_FAILURE);
}
}
