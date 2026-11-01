/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Lake

/-!
`lean --run official_code.lean <lib/lean> <out>` writes the state of the compiler's cache of
specializations of a file that sees all of them, importing `Lean` and `Lake` from the toolchain at
`<lib/lean>`, one line each: `<hash of the key> <declaration>`. This is what a compiler reuses
(`Lean.Compiler.LCNF.Specialize.findSpecCache?`) in non-module files and through `import all`.
-/

open Lean Compiler LCNF Specialize

unsafe def main (args : List String) : IO Unit := do
  let [lib, out] := args | throw <| .userError "usage: <lib/lean> <out>"
  searchPathRef.set [lib]
  enableInitializersExecution
  let env ← importModules #[{ module := `Lean }, { module := `Lake }] {} (loadExts := true)
  let ext ← IO.ofExcept <| env.evalConst (SimplePersistentEnvExtension CacheEntry Cache) {}
    (mkPrivateNameCore `Lean.Compiler.LCNF.Specialize `Lean.Compiler.LCNF.Specialize.specCacheExt)
  IO.FS.withFile out .write fun h => do
    for (key, name) in (ext.getState env).map₁.toList do
      h.putStrLn s!"{key.hash} {name}"
