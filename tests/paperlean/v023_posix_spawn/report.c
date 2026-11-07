#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

static char kind(int fd, dev_t null_device) {
    struct stat st;
    if (fstat(fd, &st) != 0) return errno == EBADF ? 'C' : '?';
    if (S_ISCHR(st.st_mode) && st.st_rdev == null_device) return 'N';
    if (S_ISFIFO(st.st_mode)) return 'P';
    return 'O';
}
int main(int argc, char **argv) {
    if (argc > 2 && !strcmp(argv[1], "--execvp-reference")) {
        execvp(argv[2], argv + 2);
        return 255;
    }
    struct stat st;
    if (argc != 3 || strcmp(argv[2], "two words") != 0 || stat("/dev/null", &st) != 0) return 1;
    char kinds[4] = {0};
    for (int i = 0; i < 3; ++i) kinds[i] = kind(i, st.st_rdev);
    int extra_null = 0;
    for (int fd = 3; fd < 1024; ++fd) if (kind(fd, st.st_rdev) == 'N') ++extra_null;
    FILE *out = fopen(argv[1], "w");
    if (!out) return 2;
    fprintf(out, "%s %d %d %s %s %s\n", kinds, extra_null,
            getsid(0) == getpid() && getpgrp() == getpid(),
            getenv("U06_JOIN") ? getenv("U06_JOIN") : "missing",
            getenv("U06_PARENT") ? getenv("U06_PARENT") : "missing",
            getenv("U06_DROP") ? "still-present" : "removed");
    return fclose(out) == 0 ? 0 : 3;
}
