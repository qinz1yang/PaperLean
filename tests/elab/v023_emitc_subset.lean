module

import Lean
public meta import Lean.Compiler.LCNF.EmitC
import Lean.Compiler.LCNF.EmitUtil
import all Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.InitAttr

open Lean Compiler LCNF

set_option Elab.async false

@[noinline] def subsetHelper (n : Nat) : Nat := n + 1
@[noinline] def subsetClosed : Array Nat := #[10, 20, 30]
initialize subsetSeed : Nat ← pure 7

mutual
  @[noinline] def subsetEven : Nat → Bool
    | 0 => true
    | n + 1 => subsetOdd n
  @[noinline] def subsetOdd : Nat → Bool
    | 0 => false
    | n + 1 => subsetEven n
end

@[noinline] def subsetEntry (n : Nat) : Nat :=
  subsetHelper n + subsetSeed + subsetClosed[if subsetEven n then 0 else 1]!

public def main : IO Unit := IO.println (subsetEntry 10)

run_meta do
  let env ← getEnv
  let roots := #[``subsetEntry]
  let (locals, _) ← collectUsedDecls roots
  let names := locals.map (·.name)
  for required in [``subsetEntry, ``subsetHelper, ``subsetClosed, ``subsetSeed,
      ``subsetEven, ``subsetOdd] do
    unless names.contains required do throwError "missing local dependency {required}"
  let some initName := getInitFnNameFor? env ``subsetSeed |
    throwError "initializer fixture did not register an initializer"
  unless names.contains initName do throwError "initializer omitted from dependency closure"
  unless names.size > roots.size do throwError "fixture is not a proper subset"
  let subset ← emitCForDecls env.mainModule roots
  let complete ← emitCForDecls env.mainModule names
  let duplicate ← emitCForDecls env.mainModule (roots ++ roots)
  unless subset == complete && subset == duplicate do
    throwError "subset, complete closure, and duplicate-root emission differ"
  unless (← emitCForDecls env.mainModule roots) == subset do
    throwError "subset emission is nondeterministic"
  let all ← getLocalImpureDecls
  unless (← emitC env.mainModule) == (← emitCForDecls env.mainModule all) do
    throwError "full emission changed"
  -- External-only and empty requests have no local indices to look up.
  let (externalLocals, _) ← collectUsedDecls #[``Nat.add]
  unless externalLocals.isEmpty do throwError "imported fixture became local"
  discard <| emitCForDecls env.mainModule #[``Nat.add, ``Nat.add]
  discard <| emitCForDecls env.mainModule #[]
  -- Optionally write both C programs for native execution.
  if let some dir ← IO.getEnv "V023_EMIT_DIR" then
    let (mainLocals, _) ← collectUsedDecls #[`main]
    let a ← emitCForDecls env.mainModule #[`main]
    let b ← emitCForDecls env.mainModule (mainLocals.map (·.name))
    unless a == b do throwError "main closure emission differs"
    IO.FS.writeFile (System.FilePath.mk dir / "subset.c") a
    IO.FS.writeFile (System.FilePath.mk dir / "closure.c") b

-- This module's initializer runs in the native executable, which must print 28.
