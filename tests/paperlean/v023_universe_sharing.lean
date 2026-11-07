/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

open Lean Meta

axiom universeLeft.{u} : Type u
axiom universeRight.{u} : Type u
axiom universeWitness.{u} : Sort u → Nat
class UniverseClass (n : Nat) : Prop where
instance (x : Nat) : UniverseClass x := {}

/-- Only one new DAG node per layer. -/
private def sharedLevel (leaf : Level) : Level := Id.run do
  let mut u := leaf
  for i in [0:72] do
    u := if i % 2 == 0 then mkLevelMax u u else mkLevelIMax u u
  return u

run_meta do
  let unassigned := sharedLevel (← mkFreshLevelMVar)
  let left := mkConst ``universeLeft [unassigned]
  let right := mkConst ``universeRight [unassigned]
  unless PaperLean.mvarsInstantiated (← getMCtx) left do
    throwError "an unassigned level should leave the input unchanged"
  if ← isDefEq left right then throwError "distinct constants were unified"
  let assigned ← mkFreshLevelMVar
  assignLevelMVar assigned.mvarId! Level.one
  -- An assigned variable after an already-visited shared subgraph must still be seen.
  let mixed := mkSort (mkLevelMax unassigned (sharedLevel assigned))
  if PaperLean.mvarsInstantiated (← getMCtx) mixed then throwError "missed an assigned level"
  let instantiated ← instantiateMVars mixed
  if instantiated.equal mixed then throwError "test did not force an instantiation"
  -- A pending term in a dependent local context, plus a real expression assignment.
  withLocalDeclD `x (mkSort unassigned) fun x => do
    let v ← mkFreshExprMVar (← inferType x)
    v.mvarId!.assign x
    if PaperLean.mvarsInstantiated (← getMCtx) v then throwError "missed an assigned expression"

private def solve : MetaM Unit := do
  let leaf ← mkFreshLevelMVar
  assignLevelMVar leaf.mvarId! Level.one
  let u := sharedLevel leaf
  withLetDecl `x (mkConst ``Nat) (mkApp (mkConst ``universeWitness [mkLevelSucc u]) (mkSort u)) fun x => do
    discard <| synthInstance (mkApp (mkConst ``UniverseClass) x)
run_meta solve
run_meta solve
