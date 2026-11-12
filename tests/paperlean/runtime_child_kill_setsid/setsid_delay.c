/*
 * Test-only preload: delay the child's setsid() after writing a marker, so the parent
 * can call Child.kill while the child still belongs to the parent's process group.
 * No libc development headers are assumed; only the entry points used here are declared.
 */
typedef unsigned long size_t;
typedef long ssize_t;
typedef int pid_t;
extern char *getenv(const char *);
extern int open(const char *, int, ...);
extern ssize_t write(int, const void *, size_t);
extern int close(int);
extern int nanosleep(const void *, void *);
extern long syscall(long, ...);

struct timespec { long tv_sec; long tv_nsec; };

#if defined(__x86_64__)
#define TEST_SYS_setsid 112
#elif defined(__aarch64__)
#define TEST_SYS_setsid 157
#else
#error "this test supports Linux x86-64 and aarch64"
#endif

static const char *marker;

__attribute__((constructor)) static void test_init(void) {
    marker = getenv("PL_SETSID_MARKER");
}

pid_t setsid(void) {
    if (marker && *marker) {
        int fd = open(marker, 01 /* O_WRONLY */ | 0100 /* O_CREAT */ | 01000 /* O_TRUNC */, 0600);
        if (fd >= 0) { (void)write(fd, "x", 1); (void)close(fd); }
        struct timespec ts = { 2, 0 };
        while (nanosleep(&ts, &ts) < 0) { }
    }
    return (pid_t)syscall(TEST_SYS_setsid);
}
