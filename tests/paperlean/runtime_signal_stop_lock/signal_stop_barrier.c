/*
 * Test-only preload used by the deterministic Signal.stop race.
 *
 * The test harness marks its two stop threads with `pl_stop_enter`, and this
 * library interposes `pthread_mutex_trylock` (the operation used by the event
 * loop's lock acquisition) to hold the first two calls at a barrier.  On 0.2.3
 * both calls read the signal state (RUNNING) before entering the event-loop
 * lock, so both proceed and each drops the loop's reference.  With the fix the
 * state check happens after the lock, so the second call observes FINISHED and
 * does not drop the reference again.
 *
 * No libc development headers are assumed.
 */
typedef struct lean_object lean_object;

extern void *dlopen(const char *, int);
extern void *dlsym(void *, const char *);
extern int usleep(unsigned int);
extern int printf(const char *, ...);
extern int fflush(void *);
extern void _exit(int);

#define PL_RTLD_NOW 2
#define PL_RTLD_NOLOAD 4

typedef int (*trylock_fn)(void *);

static trylock_fn real_pthread_trylock;
static __thread int in_stop;
static volatile int armed = 2;
static volatile int arrived;
static volatile int released;

__attribute__((constructor)) static void pl_init(void) {
    void *libc = dlopen("libc.so.6", PL_RTLD_NOW | PL_RTLD_NOLOAD);
    if (!libc) libc = dlopen("libc.so.6", PL_RTLD_NOW);
    if (libc) real_pthread_trylock = (trylock_fn)dlsym(libc, "pthread_mutex_trylock");
    if (!real_pthread_trylock) {
        printf("signal barrier: pthread=%p\n", (void*)real_pthread_trylock);
        fflush((void*)0);
        _exit(99);
    }
}

static void barrier(void) {
    int n = __sync_add_and_fetch(&arrived, 1);
    if (n >= 2) __sync_lock_test_and_set(&released, 1);
    while (!__sync_add_and_fetch(&released, 0)) usleep(500);
    if (n >= 2) {
        printf("signal barrier released\n");
        fflush((void*)0);
    }
}

/* Borrowed argument: the workload keeps the signal alive. */
void pl_stop_enter(void) {
    in_stop = 1;
}

void pl_stop_leave(void) {
    in_stop = 0;
}

int pthread_mutex_trylock(void *m) {
    if (in_stop && __sync_fetch_and_sub(&armed, 1) > 0) {
        barrier();
    }
    return real_pthread_trylock(m);
}
