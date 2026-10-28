/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include <cstdlib>
#include <string>
#include <thread>
#if !defined(LEAN_WINDOWS)
#include <cerrno>
#include <signal.h>
#include <unistd.h>
#endif
#if !defined(LEAN_WINDOWS)
#include <sys/statvfs.h>
#endif
#include "runtime/object.h"
#include "runtime/io.h"
#include "paperlean/side_file.h"

// Small system functions for `Lean.PaperLean.System` and Lake's `paperlean` command.

namespace lean {
/* version : Unit → String -- `g_paperlean_version` */
extern "C" LEAN_EXPORT obj_res lean_paperlean_version(obj_arg) {
    return lean_mk_string(g_paperlean_version);
}

/* setEnv (name : @& String) (value : @& Option String) : BaseIO Unit
   Sets the variable `name` of this process to `value`, or unsets it. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_set_env(b_obj_arg name, b_obj_arg value) {
#if defined(LEAN_WINDOWS)
    _putenv_s(lean_string_cstr(name), lean_is_scalar(value) ? "" : lean_string_cstr(lean_ctor_get(value, 0)));
#else
    if (lean_is_scalar(value)) unsetenv(lean_string_cstr(name));
    else setenv(lean_string_cstr(name), lean_string_cstr(lean_ctor_get(value, 0)), 1);
#endif
    return lean_box(0);
}

/* processAlive (pid : UInt32) : BaseIO Bool -- whether a process with that id exists */
extern "C" LEAN_EXPORT uint8 lean_paperlean_process_alive(uint32_t pid) {
#if defined(LEAN_WINDOWS)
    (void)pid;
    return true;
#else
    return kill(static_cast<pid_t>(pid), 0) == 0 || errno == EPERM;
#endif
}

/* numCPUs : BaseIO Nat -- the number of hardware threads */
extern "C" LEAN_EXPORT obj_res lean_paperlean_num_cpus(obj_arg) {
    unsigned n = std::thread::hardware_concurrency();
    return lean_box(n ? n : 1);
}

/* totalMemory : BaseIO Nat -- the bytes of physical memory, 0 if unknown */
extern "C" LEAN_EXPORT obj_res lean_paperlean_total_memory(obj_arg) {
#if defined(LEAN_WINDOWS)
    return lean_box(0);
#else
    long pages = sysconf(_SC_PHYS_PAGES), size = sysconf(_SC_PAGE_SIZE);
    return lean_uint64_to_nat(pages > 0 && size > 0 ? static_cast<uint64_t>(pages) * size : 0);
#endif
}

/* freeSpace (path : @& String) : IO Nat -- bytes available to this user on the file system of `path` */
extern "C" LEAN_EXPORT obj_res lean_paperlean_free_space(b_obj_arg path) {
#if defined(LEAN_WINDOWS)
    (void)path;
    return io_result_mk_error("freeSpace: not supported on Windows");
#else
    struct statvfs st;
    if (statvfs(lean_string_cstr(path), &st) != 0)
        return io_result_mk_error((std::string("freeSpace: cannot read ") + lean_string_cstr(path)).c_str());
    return io_result_mk_ok(lean_uint64_to_nat(static_cast<uint64_t>(st.f_bavail) * st.f_frsize));
#endif
}
}
