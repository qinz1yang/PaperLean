#if defined(__linux__)
#define _GNU_SOURCE
#endif
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <unistd.h>
#include <sys/wait.h>
#if !defined(__APPLE__)
#include <dlfcn.h>
#endif

static int events[2];
static _Atomic int armed;

uint8_t u08_oracle_arm(uint8_t observe) {
    if (!observe) return 1;
    if (pipe(events) || fcntl(events[0], F_SETFD, FD_CLOEXEC) ||
        fcntl(events[1], F_SETFD, FD_CLOEXEC)) return 0;
    atomic_store(&armed, 1);
    return 1;
}

static void started(pid_t pid) {
    if (!atomic_load(&armed)) return;
    int saved = errno;
    ssize_t n;
    do { n = write(events[1], &pid, sizeof pid); } while (n < 0 && errno == EINTR);
    if (n != sizeof pid) _exit(87);
    errno = saved;
}

uint8_t u08_oracle_observer(uint32_t expected) {
    pid_t pid;
    for (;;) {
        ssize_t n;
        do { n = read(events[0], &pid, sizeof pid); } while (n < 0 && errno == EINTR);
        if (n != sizeof pid) return 0;
        if (pid == (pid_t)expected) {
            atomic_store(&armed, 0);
            return 1;
        }
    }
}

uint8_t u08_oracle_reaped(uint32_t pid) {
    int status;
    errno = 0;
    pid_t result = waitpid((pid_t)pid, &status, WNOHANG);
    int wait_errno = errno;
    errno = 0;
    int alive = kill((pid_t)pid, 0);
    int kill_errno = errno;
    if (result == -1 && wait_errno == ECHILD && alive == -1 && kill_errno == ESRCH)
        return 1;
    fprintf(stderr, "pid %u: waitpid %d errno %d, kill(0) %d errno %d\n",
            pid, (int)result, wait_errno, alive, kill_errno);
    return 0;
}

#if defined(__APPLE__)
static int u08_waitid(idtype_t type, id_t id, siginfo_t *info, int flags) {
    if (type == P_PID && (flags & WEXITED) && !(flags & WNOHANG)) started((pid_t)id);
    return waitid(type, id, info, flags);
}

static pid_t u08_waitpid(pid_t pid, int *status, int flags) {
    if (pid > 0 && !(flags & WNOHANG)) started(pid);
    return waitpid(pid, status, flags);
}

#define INTERPOSE(new_fn, old_fn) \
    __attribute__((used, section("__DATA,__interpose"))) static const struct { \
        const void *replacement; const void *original; \
    } u08_hook_##old_fn = { (const void *)&new_fn, (const void *)&old_fn }
INTERPOSE(u08_waitid, waitid);
INTERPOSE(u08_waitpid, waitpid);
#else
int waitid(idtype_t type, id_t id, siginfo_t *info, int flags) {
    int (*actual)(idtype_t, id_t, siginfo_t *, int) = dlsym(RTLD_NEXT, "waitid");
    if (!actual) _exit(88);
    if (type == P_PID && (flags & WEXITED) && !(flags & WNOHANG)) started((pid_t)id);
    return actual(type, id, info, flags);
}

pid_t waitpid(pid_t pid, int *status, int flags) {
    pid_t (*actual)(pid_t, int *, int) = dlsym(RTLD_NEXT, "waitpid");
    if (!actual) _exit(88);
    if (pid > 0 && !(flags & WNOHANG)) started(pid);
    return actual(pid, status, flags);
}
#endif
