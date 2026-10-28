/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <string>
#include <vector>
#if defined(__APPLE__)
#include <crt_externs.h>
#include <mach-o/dyld.h>
#endif
#if !defined(LEAN_WINDOWS)
#include <unistd.h>
#endif
#include "runtime/object.h"

// Re-running `lean` with reuse off, for `Lean.PaperLean.Speculation`.

namespace lean {
/* reexecExact : BaseIO Bool
   Replaces this process by a run of the same executable with the same arguments and `PAPERLEAN_EXACT=1`
   in its environment. Returns `false` only if that is not possible. */
extern "C" LEAN_EXPORT uint8 lean_paperlean_reexec_exact() {
#if defined(LEAN_WINDOWS)
    return false;
#else
    std::vector<std::string> args;
    std::string exe;
#if defined(__APPLE__)
    int argc = *_NSGetArgc();
    char ** argv = *_NSGetArgv();
    for (int i = 0; i < argc; i++) args.push_back(argv[i]);
    uint32_t size = 0;
    _NSGetExecutablePath(nullptr, &size);
    std::vector<char> path(size + 1, '\0');
    if (_NSGetExecutablePath(path.data(), &size) != 0) return false;
    exe = path.data();
#else
    std::ifstream in("/proc/self/cmdline", std::ios::binary);
    std::string arg;
    while (std::getline(in, arg, '\0')) args.push_back(arg);
    exe = "/proc/self/exe";
#endif
    if (args.empty()) return false;
    std::vector<char *> argv2;
    for (std::string & a : args) argv2.push_back(&a[0]);
    argv2.push_back(nullptr);
    if (setenv("PAPERLEAN_EXACT", "1", 1) != 0) return false;
    fflush(stdout);
    fflush(stderr);
    execv(exe.c_str(), argv2.data());
    unsetenv("PAPERLEAN_EXACT");
    return false;
#endif
}
}
