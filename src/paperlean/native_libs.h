/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#pragma once
#include <lean/lean.h>

namespace lean {
// Native libraries of packages (`native_libs.cpp`).

// `addr`, the native code that the interpreter found for `fn` in an environment `env`, unless it lies in
// a native library that PaperLean loaded, or in one it pulled in, and is not the code of that library
// for an imported module of `env` that the library was verified for; then `nullptr`.
void * filter_native_symbol(b_lean_obj_arg env, b_lean_obj_arg fn, void * addr);
// `addr`, the module initializer `sym`, unless it lies in such a library and is not the initializer
// of that library for a module of the import being finalized on this thread that uses its native
// code; then `nullptr`.
void * filter_native_initializer(char const * sym, void * addr);
}
