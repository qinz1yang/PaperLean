/*
 * Regression test for Signal.stop racing with the event-loop callback.
 *
 * Deterministic phase (Linux, with the preload): two threads call
 * Signal.stop on the same running signal.  The preload holds both calls at a
 * barrier inside the event-loop lock acquisition, after 0.2.3 has already read
 * the unlocked state.  Both calls then drop the loop's reference.  The test
 * checks the external's reference count before releasing its own references:
 * two caller references must remain (one per caller); 0.2.3 leaves one.
 *
 * Stress phase: repeatedly raise a one-shot signal and stop it immediately,
 * which races the libuv callback against stop.  0.2.3 usually segfaults here.
 *
 * No libc development headers are assumed.
 */
#include <lean/lean.h>

extern int printf(const char *, ...);
extern int fflush(void *);
extern int raise(int);
extern void _exit(int);
extern void lean_initialize_runtime_module(void);
extern void lean_init_task_manager_using(unsigned);
extern lean_object * lean_uv_signal_mk(uint32_t, uint8_t);
extern lean_object * lean_uv_signal_next(lean_object *);
extern lean_object * lean_uv_signal_stop(lean_object *);

typedef unsigned long pthread_t;
extern int pthread_create(pthread_t *, const void *, void *(*)(void *), void *);
extern int pthread_join(pthread_t, void **);

#ifdef __linux__
extern void pl_stop_enter(void);
extern void pl_stop_leave(void);
#define TEST_HAVE_BARRIER 1
#else
#define TEST_HAVE_BARRIER 0
#endif

#define LEAN_SIGUSR1 10
#ifdef __APPLE__
#define NATIVE_SIGUSR1 30
#else
#define NATIVE_SIGUSR1 10
#endif

static lean_object *shared_signal;

static void *stop_worker(void *arg) {
    (void)arg;
#if TEST_HAVE_BARRIER
    pl_stop_enter();
#endif
    lean_object *r = lean_uv_signal_stop(shared_signal);
#if TEST_HAVE_BARRIER
    pl_stop_leave();
#endif
    if (r) lean_dec(r);
    return 0;
}

static int reference_count(lean_object *o) {
    int rc = lean_internal_get_rc(o);
    return rc < 0 ? -rc : rc;
}

static int deterministic_double_stop(void) {
    lean_object *mr = lean_uv_signal_mk(LEAN_SIGUSR1, 0);
    if (!lean_io_result_is_ok(mr)) { printf("mk failed\n"); return 2; }
    lean_object *sig = lean_io_result_get_value(mr);

    lean_object *pr = lean_uv_signal_next(sig);
    if (!lean_io_result_is_ok(pr)) { printf("next failed\n"); return 2; }
    lean_object *promise = lean_io_result_get_value(pr);

    /* One reference for the caller, one extra so the object survives the
       double drop while the test inspects its count, and one owned by the loop
       (taken by `next`). */
    lean_inc(sig);
    shared_signal = sig;
    pthread_t a, b;
    if (pthread_create(&a, 0, stop_worker, 0) != 0 ||
        pthread_create(&b, 0, stop_worker, 0) != 0) {
        printf("pthread_create failed\n");
        return 2;
    }
    pthread_join(a, 0);
    pthread_join(b, 0);

    int refs = reference_count(sig);
    printf("deterministic double stop: refs=%d (expected 2)\n", refs);
    if (refs != 2) {
        printf("FAIL: two concurrent Signal.stop calls dropped the loop reference twice\n");
        fflush((void*)0);
        _exit(1);
    }

    lean_dec(sig);   /* extra caller reference */
    lean_dec(sig);   /* original caller reference */
    lean_dec(promise);
    return 0;
}

static int stress_callback_race(void) {
    for (int i = 0; i < 5000; i++) {
        lean_object *r = lean_uv_signal_mk(LEAN_SIGUSR1, 0);
        if (!lean_io_result_is_ok(r)) { printf("mk failed at %d\n", i); return 2; }
        lean_object *sig = lean_io_result_get_value(r);
        lean_object *pr = lean_uv_signal_next(sig);
        if (!lean_io_result_is_ok(pr)) { printf("next failed at %d\n", i); return 2; }
        lean_object *promise = lean_io_result_get_value(pr);

        raise(NATIVE_SIGUSR1);
        lean_object *sr = lean_uv_signal_stop(sig);
        if (!lean_io_result_is_ok(sr)) { printf("stop failed at %d\n", i); return 2; }

        lean_dec(sr);
        lean_dec(promise);
        lean_dec(sig);
    }
    printf("stress completed\n");
    fflush((void*)0);
    return 0;
}

int main(void) {
    lean_initialize_runtime_module();
    lean_init_task_manager_using(2);
    int r = deterministic_double_stop();
    if (r != 0) return r;
    return stress_callback_race();
}
