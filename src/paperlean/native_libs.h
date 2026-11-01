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
// Called before Lean loads a shared library (`Dynlib.load`: `--load-dynlib`, plugins, the dynlibs
// of a module's setup, `Lean.loadDynlib`), whose code may have any package's symbols.
void note_dynlib_load();
// Whether `filter_native_symbol` drops whatever the interpreter can find for `fn`, an imported
// declaration of `env` without an `@[export]` name: `fn` belongs to a package's module whose
// initializer is in such a library, so that the module's symbols, which have the package's prefix,
// are found there or nowhere (Lean's own code has no such symbols, and a library loaded before it
// that had any of the module's code would have its initializer too), and the module's native code
// is not used for `fn`; never after Lean loaded a shared library (`note_dynlib_load`).
bool skip_native_lookup(b_lean_obj_arg env, b_lean_obj_arg fn);
// The module initializer `sym` as `dlsym(RTLD_DEFAULT, sym)` finds it now if the import being
// finalized on this thread found it already when it loaded these libraries; otherwise `nullptr`.
void * found_native_initializer(char const * sym);
// `addr`, the module initializer `sym`, unless it lies in such a library and is not the initializer
// of that library for a module of the import being finalized on this thread that uses its native
// code; then `nullptr`.
void * filter_native_initializer(char const * sym, void * addr);
}
