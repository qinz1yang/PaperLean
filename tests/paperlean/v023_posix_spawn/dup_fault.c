// Test-only failures in the forked child, before it replaces its image.
#include <errno.h>
#include <fcntl.h>
#include <stdarg.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>
static pid_t driver;
#ifdef __APPLE__
#define real_open open
#define real_dup2 dup2
#define test_open_name test_open
#define test_dup2_name test_dup2
#else
#include <dlfcn.h>
static int (*real_open)(const char *, int, ...);
static int (*real_dup2)(int, int);
#define test_open_name open
#define test_dup2_name dup2
#endif
__attribute__((constructor)) static void init_hooks(void) {
    driver = getpid();
#ifndef __APPLE__
    real_open = dlsym(RTLD_NEXT, "open");
    real_dup2 = dlsym(RTLD_NEXT, "dup2");
#endif
}
int test_open_name(const char *path, int flags, ...) {
    if (driver != getpid() && (flags & O_ACCMODE) == O_RDONLY && !strcmp(path, "/dev/null")) {
        errno = EMFILE; return -1;
    }
    int needs_mode = flags & O_CREAT;
#ifdef O_TMPFILE
    needs_mode |= ((flags & O_TMPFILE) == O_TMPFILE);
#endif
    if (needs_mode) {
        va_list ap;
        va_start(ap, flags);
        int mode = va_arg(ap, int);
        va_end(ap);
        return real_open(path, flags, mode);
    }
    return real_open(path, flags);
}
int test_dup2_name(int from, int to) {
    if (driver != getpid() && to == STDOUT_FILENO) { errno = EBADF; return -1; }
    return real_dup2(from, to);
}
#ifdef __APPLE__
__attribute__((used, section("__DATA,__interpose"))) static const struct {
    int (*replacement)(const char *, int, ...); int (*original)(const char *, int, ...);
} open_hook = { test_open, open };
__attribute__((used, section("__DATA,__interpose"))) static const struct {
    int (*replacement)(int, int); int (*original)(int, int);
} dup2_hook = { test_dup2, dup2 };
#endif
