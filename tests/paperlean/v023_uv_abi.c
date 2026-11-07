/* Copyright (c) 2026 PaperLean contributors. Released under the Apache 2.0 license. */
#include <lean/lean.h>
#include <errno.h>
#include <stdio.h>

extern void lean_initialize_runtime_module(void);
extern lean_object *lean_uv_event_loop_configure(lean_object *);
extern lean_object *l_Std_Internal_UV_Loop_configure___boxed(lean_object *, lean_object *);
extern lean_object *lean_uv_event_loop_configure_checked(lean_object *);
extern uint8_t lean_uv_event_loop_alive(void);

#ifdef UV_ABI_INJECT
static int fail_at, calls, failures;
/* Linked only by the fault-injected build of the real event-loop source. */
int v023_uv_configuration_result(int option) {
    (void)option;
    ++calls;
    if (calls == fail_at) {
        ++failures;
        return -EINVAL;
    }
    return 0;
}
#endif

static lean_object *options(int enable) {
    lean_object *value = lean_alloc_ctor(0, 0, 2);
    lean_ctor_set_uint8(value, 0, enable);
    lean_ctor_set_uint8(value, 1, enable);
    return value;
}

static int exercise(int at) {
    lean_object *opt = options(at != 0);
    for (int route = 0; route < 3; ++route) {
#ifdef UV_ABI_INJECT
        fail_at = at;
        calls = failures = 0;
#endif
        if (route < 2) {
            lean_inc(opt); /* the legacy entry owns its argument */
            lean_object *unit = route == 0
                ? lean_uv_event_loop_configure(opt)
                : l_Std_Internal_UV_Loop_configure___boxed(opt, lean_box(0));
            if (unit != lean_box(0) || !lean_is_exclusive(opt)) return 1 + route;
        } else {
            lean_object *result = lean_uv_event_loop_configure_checked(opt);
            if (!lean_is_exclusive(opt)) return 3;
            if (at ? !lean_io_result_is_error(result) :
                     !lean_io_result_is_ok(result) || lean_io_result_get_value(result) != lean_box(0))
                return 4;
            lean_dec(result);
        }
#ifdef UV_ABI_INJECT
        if (calls != at || failures != (at != 0)) return 5;
#endif
        (void)lean_uv_event_loop_alive(); /* the same lock must be usable after any failure */
    }
    lean_dec(opt);
    return 0;
}

int main(void) {
    lean_initialize_runtime_module();
    int status = exercise(0);
#ifdef UV_ABI_INJECT
    if (!status) status = exercise(1); /* metrics */
    if (!status) status = exercise(2); /* POSIX block signal */
#endif
    if (status) fprintf(stderr, "UV configure ABI failed at check %d\n", status);
    return status;
}
