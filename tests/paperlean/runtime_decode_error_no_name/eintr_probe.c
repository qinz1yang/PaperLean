/*
 * Regression test for decode_io_error(errno, nullptr) in the EINTR and ENOENT
 * branches.  The direct decoder calls pass no file name; the flock case reaches
 * the same decoder through the public Handle.lock operation.  Before the fix
 * both branches incremented a null file-name object and crashed.
 *
 * No libc development headers are assumed: the small set of entry points used
 * here is declared explicitly.
 */
#include <lean/lean.h>

extern int printf(const char *, ...);
extern int fflush(void *);
extern int mkstemp(char *);
extern int close(int);
extern void _exit(int);
extern int pipe(int *);
extern int fork(void);
extern int open(const char *, int, ...);
extern int flock(int, int);
extern int usleep(unsigned int);
extern long read(int, void *, unsigned long);
extern long write(int, const void *, unsigned long);
extern int waitpid(int, int *, int);
extern int kill(int, int);
extern int getppid(void);
extern int siginterrupt(int, int);

typedef int pid_t;
typedef void (*test_sighandler)(int);
extern test_sighandler signal(int, test_sighandler);
extern void lean_initialize_runtime_module(void);
extern lean_object * lean_decode_uv_error(int, lean_object *);
extern lean_object * lean_io_prim_handle_mk(lean_object *, uint8_t);
extern lean_object * lean_io_prim_handle_lock(lean_object *, uint8_t);

#ifdef __APPLE__
#define TEST_SIGUSR1 30
#else
#define TEST_SIGUSR1 10
#endif

static void on_usr1(int sig) { (void)sig; }

static int decode_cases(void) {
    /* `lean_decode_uv_error` returns an `IO.Error`, not an `IO` result: the
       constructors for EINTR and ENOENT are `interrupted` (tag 10) and
       `noFileOrDirectory` (tag 11).  Before the fix the decoder crashed while
       incrementing the null file-name object. */
    lean_object * e = lean_decode_uv_error(-4 /* UV_EINTR */, NULL);
    if (e == NULL || lean_obj_tag(e) != 10) {
        printf("EINTR decoder returned the wrong error object\n");
        return 1;
    }
    lean_dec(e);
    printf("decode EINTR ok\n");

    e = lean_decode_uv_error(-2 /* UV_ENOENT */, NULL);
    if (e == NULL || lean_obj_tag(e) != 11) {
        printf("ENOENT decoder returned the wrong error object\n");
        return 1;
    }
    lean_dec(e);
    printf("decode ENOENT ok\n");
    return 0;
}

static int interrupted_lock(void) {
    char tmpl[] = "lean-eintr-XXXXXX";
    int fd = mkstemp(tmpl);
    if (fd < 0) { printf("mkstemp failed\n"); return 2; }
    close(fd);

    lean_object * path = lean_mk_string(tmpl);
    lean_object * r = lean_io_prim_handle_mk(path, 3 /* readWrite */);
    lean_dec(path);
    if (!lean_io_result_is_ok(r)) { printf("handle mk failed\n"); return 2; }
    lean_object * h = lean_io_result_get_value(r);

    int ready[2], go[2];
    if (pipe(ready) != 0 || pipe(go) != 0) { printf("pipe failed\n"); return 2; }
    pid_t pid = fork();
    if (pid == 0) {
        close(ready[0]);
        close(go[1]);
        int cfd = open(tmpl, 2 /* O_RDWR */);
        if (cfd < 0) _exit(3);
        if (flock(cfd, 2 /* LOCK_EX */) != 0) _exit(4);
        char c = 'r';
        if (write(ready[1], &c, 1) != 1) _exit(5);
        if (read(go[0], &c, 1) != 1) _exit(6);
        /* The parent is entering flock() now.  Keep the lock for long enough to
           guarantee that at least one signal arrives while it is blocked. */
        for (int i = 0; i < 100; i++) {
            usleep(10000);
            kill(getppid(), TEST_SIGUSR1);
        }
        _exit(0);
    }
    close(ready[1]);
    close(go[0]);
    char c;
    if (read(ready[0], &c, 1) != 1) { printf("child did not lock\n"); return 2; }
    close(ready[0]);

    if (signal(TEST_SIGUSR1, on_usr1) == (test_sighandler)-1) {
        printf("signal failed\n"); return 2;
    }
    if (siginterrupt(TEST_SIGUSR1, 1) != 0) { printf("siginterrupt failed\n"); return 2; }

    char g = 'g';
    if (write(go[1], &g, 1) != 1) { printf("go write failed\n"); return 2; }
    close(go[1]);

    lean_object * lr = lean_io_prim_handle_lock(h, 1);
    int ok = lr != NULL && lean_io_result_is_ok(lr);
    printf("lock returned: ok=%d\n", ok);
    if (lr != NULL) lean_dec(lr);
    lean_dec(h);

    /* The child sends repeated signals; wait through the EINTRs it causes. */
    for (int i = 0; i < 1000; i++) {
        int status = 0;
        pid_t w = waitpid(pid, &status, 0);
        if (w == pid) break;
    }
    if (ok) {
        printf("Handle.lock succeeded while another process held the lock\n");
        return 1;
    }
    printf("interrupted lock ok\n");
    return 0;
}

int main(int argc, char ** argv) {
    lean_initialize_runtime_module();
    if (argc > 1 && argv[1][0] == 'd' && argv[1][1] == 'e') return decode_cases();
    if (argc > 1 && argv[1][0] == 'f') return interrupted_lock();
    printf("usage: eintr_probe decode|flock\n");
    return 2;
}
