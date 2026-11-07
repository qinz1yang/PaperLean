// Copyright (c) 2026 PaperLean contributors.
// Released under Apache 2.0 license as described in the file LICENSE.
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <future>
#include <thread>
#include "runtime/alloc.h"
#include "runtime/interrupt.h"
#include "runtime/object.h"
#include "runtime/thread.h"

namespace lean {
extern "C" size_t lean_paperlean_swap_kernel_heartbeats(size_t n);
extern "C" obj_res lean_paperlean_trial_proofs(obj_arg env, size_t normal_limit, size_t max_depth,
                                              b_obj_arg decls, b_obj_arg cancel);

static void require(bool ok, char const * what) {
    if (!ok) { std::fprintf(stderr, "failed: %s\n", what); std::exit(2); }
}

extern "C" obj_res lean_add_decl(obj_arg env, size_t normal, size_t depth, b_obj_arg decl, b_obj_arg cancel);

// Measure a genuine singleton's kernel checks so the aggregate boundary test does not depend
// on a particular compiler version's check count.
extern "C" size_t paperlean_test_stock_proof_cost(obj_arg env, b_obj_arg decl) {
    uint64_t alloc = get_num_heartbeats();
    size_t old = lean_paperlean_swap_kernel_heartbeats(0);
    object * result = lean_add_decl(env, 0, 20000, decl, lean_box(0));
    size_t cost = lean_paperlean_swap_kernel_heartbeats(old);
    require(lean_obj_tag(result) == 1 && cost > 0, "singleton stock control");
    lean_dec(result);
    set_heartbeats(alloc);
    return cost;
}

extern "C" obj_res paperlean_test_proof_budget(obj_arg env, size_t normal, size_t ambient, size_t spent,
                                               b_obj_arg decls, b_obj_arg cancel, b_obj_arg parent) {
    constexpr uint64_t allocation_stamp = 12931037;
    uint64_t original = get_num_heartbeats();
    size_t kernel = lean_paperlean_swap_kernel_heartbeats(spent);
    scope_max_heartbeat max(ambient);
    scope_cancel_tk token(cnstr_get(parent, 0));
    set_heartbeats(allocation_stamp);
    object * result = lean_paperlean_trial_proofs(env, normal, 20000, decls, cancel);
    require(get_num_heartbeats() == allocation_stamp, "allocation heartbeat");
    require(lean_paperlean_swap_kernel_heartbeats(kernel) == spent, "kernel heartbeat");
    require(get_max_heartbeat() == ambient, "outer maximum");
    bool restored = false;
    try { check_interrupted(); } catch (interrupted const &) { restored = true; }
    require(restored, "outer cancellation token");
    set_heartbeats(original);
    return result;
}
}

extern "C" uint8_t paperlean_test_cancel_poll(b_lean_obj_arg tk) {
    lean_object *flag = lean_ctor_get(tk, 1);
    lean_mark_mt(flag);
    lean::scope_cancel_tk token(tk);
    auto poll = []() {
        try { lean::check_interrupted(); }
        catch (lean::interrupted const &) { return true; }
        return false;
    };

    bool before = poll();
    std::promise<void> taken, done;
    auto doneSignal = done.get_future();
    auto takenSignal = taken.get_future();
    std::thread reader([&] {
        lean::lean_initialize_thread();
        lean_object *value = lean_st_ref_take(flag);
        taken.set_value();
        // Emulate a descheduled shared IO.Ref.get, which takes the same value
        // across io.cpp's two exchanges. A fixed poll waits for restoration.
        doneSignal.wait_for(std::chrono::milliseconds(500));
        lean_dec(lean_st_ref_put(flag, value));
        lean::lean_finalize_thread();
    });
    takenSignal.wait();
    bool during = poll();
    done.set_value();
    reader.join();
    bool after = poll();
    return (before << 2) | (during << 1) | after;
}
