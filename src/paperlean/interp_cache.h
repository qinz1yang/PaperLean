/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#pragma once
#include <lean/lean.h>

namespace lean {
// What an interpreter's `lookup_symbol` (`library/ir_interpreter.cpp`) finds for a function: its IR
// declaration and its native code, if any.
struct shared_symbol {
    lean_object * decl;
    void * addr;
    bool boxed;
};

// The interpreters of environments with the same imports share what they find for imported
// declarations, which does not change: the IR declaration (from the imported modules) and the native
// symbol (which the interpreter's process-wide native symbol cache already shares). Only for imports
// whose module data is persistent, which is never freed.

// The entry of `fn` that an interpreter of an environment with the same imports as `env` found.
bool find_shared_symbol(b_lean_obj_arg env, b_lean_obj_arg fn, shared_symbol & s);
// Shares `s` for `fn` if `fn` is an imported declaration of `env`.
void share_symbol(b_lean_obj_arg env, b_lean_obj_arg fn, shared_symbol const & s);
}
