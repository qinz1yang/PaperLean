# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# PaperLean's own recursive specializations need the current module's cache, while imported
# specializations of its code must stay out of the cache used by downstream modules.

cat > "$TMP_DIR/OwnSpecialization.lean" <<'EOF2'
import Lean

/-!
Tests local specialization-cache insertion in PaperLean's namespace, the imported-entry boundary,
and compilation of a fresh recursive specialization in that namespace.
-/

namespace Lean.PaperLean.SpecializationRegression

@[noinline] def step (n : Nat) : Nat := n + 1

@[specialize] private def fold (f : Nat → Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => f x + fold f xs

def total (xs : List Nat) : Nat := fold step xs

end Lean.PaperLean.SpecializationRegression

open Lean Compiler LCNF Specialize

unsafe def main : IO Unit := do
  let own : CacheEntry := {
    key := mkConst `Nat
    declName := `Lean.PaperLean.SpecializationRegression.total
  }
  let ordinary : CacheEntry := { key := mkConst `Bool, declName := `Nat.add }
  let imported : Cache := {}
  unless (addEntry imported own).find? own.key == none do
    throw <| IO.userError "an imported PaperLean specialization was retained"
  unless (addEntry imported ordinary).find? ordinary.key == some ordinary.declName do
    throw <| IO.userError "an ordinary imported specialization was lost"
  let localCache := imported.switch
  unless (addEntry localCache own).find? own.key == some own.declName do
    throw <| IO.userError "a local PaperLean specialization was lost"
  unless (addEntry localCache ordinary).find? ordinary.key == some ordinary.declName do
    throw <| IO.userError "an ordinary local specialization was lost"
  enableInitializersExecution
  let env ← importModules #[{ module := `Lean }] {} (loadExts := true)
  let ext ← IO.ofExcept <| env.evalConst (SimplePersistentEnvExtension CacheEntry Cache) {}
    (mkPrivateNameCore `Lean.Compiler.LCNF.Specialize `Lean.Compiler.LCNF.Specialize.specCacheExt)
  let env := ext.addEntry env own
  unless (ext.getState env).find? own.key == some own.declName do
    throw <| IO.userError "the compiler's registered cache lost a local specialization"
  unless PaperLean.SpecializationRegression.total [1, 2, 3] == 9 do
    throw <| IO.userError "the recursive specialization changed its result"
  IO.println "ok"
EOF2
cd "$TMP_DIR"
capture_exit 0 lean OwnSpecialization.lean -o OwnSpecialization.olean -c OwnSpecialization.c
capture_exit 0 lean --run OwnSpecialization.lean
check_out_contains "ok"
