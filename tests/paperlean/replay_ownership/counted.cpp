/* Copyright (c) 2026 PaperLean contributors. Released under Apache 2.0 license. */
#include <atomic>
#include <lean/lean.h>

namespace {
std::atomic<bool> watching{false};
std::atomic<unsigned> constructed{0}, finalized{0};

lean_object * counted_ctor(unsigned tag, unsigned fields, unsigned bytes) {
    // The production simp replay materializes a six-field constructor. Give the test's
    // otherwise ordinary result one extra child whose destruction is observable.
    if (!watching.load() || tag != 0 || fields != 6 || bytes != 0)
        return lean_alloc_ctor(tag, fields, bytes);
    static auto * cls = lean_register_external_class(
        [](void *) { ++finalized; }, [](void *, lean_object *) {});
    auto * r = lean_alloc_ctor(tag, fields + 1, bytes);
    lean_ctor_set(r, fields, lean_alloc_external(cls, nullptr));
    ++constructed;
    return r;
}
}

#define lean_alloc_ctor counted_ctor
#include "paperlean/import_state.cpp"
#undef lean_alloc_ctor

extern "C" LEAN_EXPORT uint8_t paperlean_test_replay_ownership(b_lean_obj_arg ext, b_lean_obj_arg as) {
    using namespace lean;
    lean_inc(ext);
    object * opt = lean_paperlean_imported_state_initial(ext);
    if (lean_is_scalar(opt)) return 0;
    object_ref initial(lean_ctor_get(opt, 0), true);
    lean_dec(opt);
    watching = true;

    // Releasing at import exit and rejecting a replay with a different initial state
    // must each destroy the fresh result. An actual image must admit both launches.
    lean_paperlean_prefetch_imported_state(ext, as, 1);
    lean_paperlean_drop_prefetched_replays(lean_box(0));
    lean_paperlean_prefetch_imported_state(ext, as, 1);
    if (take_prefetched(ext, lean_box(0), as)) return 0;
    if (constructed != 2 || finalized != 2) {
        std::fprintf(stderr, "discarded: %u constructed, %u finalized\n", constructed.load(), finalized.load());
        return 0;
    }

    for (bool persistent : {false, true}) {
        lean_paperlean_prefetch_imported_state(ext, as, persistent);
        object * r = take_prefetched(ext, initial.raw(), as);
        if (!r || lean_is_persistent(r) != persistent) return 0;
        if (lean_ctor_num_objs(r) != 7 || lean_is_persistent(lean_ctor_get(r, 6)) != persistent) return 0;
        lean_dec(r);
    }
    watching = false;
    return constructed == 4 && finalized == 3;
}
