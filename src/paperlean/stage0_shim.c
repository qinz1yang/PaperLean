/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
// Loaded into the stage0 `lean` that builds stage1 (`--load-dynlib`, `src/CMakeLists.txt`): when it
// interprets stage1's code, it finds these implementations of `Lean.PaperLean.envRecording` and
// `Lean.PaperLean.nativeAvailable`, whose native code stage0 does not have: no thread of that
// process records (`Lean.PaperLean.EnvDeps`), and stage1's code takes Lean's paths instead of
// PaperLean's native code. The arguments are not released, so that this file needs nothing of the
// runtime.
void * l_Lean_PaperLean_envRecording___boxed(void * type, void * dummy) {
    (void)type;
    (void)dummy;
    return (void *)1; /* `lean_box(false)` */
}

void * l_Lean_PaperLean_nativeAvailable___boxed(void * type, void * dummy) {
    (void)type;
    (void)dummy;
    return (void *)1; /* `lean_box(false)` */
}
