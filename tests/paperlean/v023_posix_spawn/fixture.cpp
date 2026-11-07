#include <lean/lean.h>
#include <cerrno>
#include <iostream>
#include <unistd.h>

extern "C" LEAN_EXPORT lean_obj_res u06_posix_close_stdio(uint32_t mask) {
    bool ok = true;
    for (int fd = 0; fd < 3; ++fd)
        if ((mask & (1u << fd)) && close(fd) < 0 && errno != EBADF) ok = false;
    return lean_io_result_mk_ok(lean_box(ok));
}
extern "C" LEAN_EXPORT lean_obj_res u06_posix_buffer_mark() {
    std::cout << "u06-parent-buffer";
    return lean_io_result_mk_ok(lean_box(0));
}
extern "C" LEAN_EXPORT lean_obj_res u06_posix_flush_mark() {
    std::cout.flush();
    return lean_io_result_mk_ok(lean_box(0));
}
