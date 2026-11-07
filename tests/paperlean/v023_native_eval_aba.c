// macOS test interposer: only the requested module opens in the other directory.
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;
static _Thread_local int active;

static void swap_dirs(void) {
    if (renamex_np(getenv("EVAL_ABA_LIVE"), getenv("EVAL_ABA_OTHER"), RENAME_SWAP) != 0) {
        perror("swapping eval test inputs");
        _exit(83);
    }
}

static int begin(const char *path) {
    const char *target = getenv("EVAL_ABA_TARGET");
    if (active || !target || strcmp(path, target) != 0) return 0;
    pthread_mutex_lock(&lock);
    active = 1;
    swap_dirs();
    return 1;
}

static void end(int swapped) {
    if (!swapped) return;
    int saved_errno = errno;
    swap_dirs();
    active = 0;
    pthread_mutex_unlock(&lock);
    fputs("eval ABA: opened replacement\n", stderr);
    errno = saved_errno;
}

static int test_open(const char *path, int flags, ...) {
    int mode = 0;
    if (flags & O_CREAT) {
        va_list args;
        va_start(args, flags);
        mode = va_arg(args, int);
        va_end(args);
    }
    int swapped = begin(path);
    int fd = open(path, flags, mode);
    end(swapped);
    return fd;
}

static FILE *test_fopen(const char *path, const char *mode) {
    int swapped = begin(path);
    FILE *f = fopen(path, mode);
    end(swapped);
    return f;
}

__attribute__((used, section("__DATA,__interpose")))
static const struct { const void *replacement, *original; } hooks[] = {
    {(const void *)&test_open, (const void *)&open},
    {(const void *)&test_fopen, (const void *)&fopen}
};
