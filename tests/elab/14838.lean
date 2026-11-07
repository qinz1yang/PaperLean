import Lean

open Lean

set_option Elab.async false

/-!
Regression for the reference-count overflow of #14383. The daily test uses depth 12.
The separate `tests/stress/rc_overflow.py` runner uses depth 30 with time and resource limits;
actual overflow reproduction requires roughly 12GB of free RAM.

`maxDag` builds a `Level` DAG that expands to `2 ^ depth` occurrences of a single shared leaf, so
checking a declaration whose type mentions it drives that leaf object's 32-bit reference count past
`INT_MAX`. The wrapped count corrupts the object, and the kernel accepts `Candidate.{u} : Enc.{u}.val`
even though the proof only establishes `Enc.{0}.val`; `Candidate.{1}` then yields `False`.
-/

namespace RCOverflow

def AllSubsingleton.{u} : Prop :=
  ∀ (α : Sort u) (x y : α), x = y

opaque Enc.{u} : { p : Prop // p = AllSubsingleton.{u} } :=
  ⟨AllSubsingleton.{u}, rfl⟩

theorem encSpec.{u} : Enc.{u}.val = AllSubsingleton.{u} :=
  Enc.{u}.property

theorem allZero : AllSubsingleton.{0} := by
  intro α x y
  rfl

theorem encZero : Enc.{0}.val :=
  Eq.mpr encSpec.{0} allZero

theorem encOneFalse (value : Enc.{1}.val) : False :=
  Bool.noConfusion ((Eq.mp encSpec.{1} value) Bool false true)

private def candidateName := `RCOverflow.Candidate

private def controlName := `RCOverflow.Control

private def depth := 12

private def maxDag (leaf : Level) : Nat → Level
  | 0 => leaf
  | depth + 1 => let previous := maxDag leaf depth; Level.max previous previous

private def paddingTree (first : Nat) : Nat → Expr
  | 0 => mkRawNatLit first
  | depth + 1 => mkApp2 (mkConst ``Nat.add)
      (paddingTree first depth) (paddingTree (first + 2^depth) depth)

private def targetType (dag : Level) (paddingDepth : Nat) : Expr :=
  mkLet `u (mkConst ``PUnit [dag]) (mkConst ``PUnit.unit [dag])
    (mkLet `padding (mkConst ``Nat) (paddingTree 1 paddingDepth)
      (mkProj ``Subtype 0 (mkConst ``Enc [dag])) true) true

private def perform (env : Environment) (name : Name) (leaf : Level) (depth paddingDepth : Nat) :
    IO (Except Kernel.Exception Environment) := do
  let declaration : Declaration := .thmDecl {
    name, levelParams := [`u]
    type := targetType (maxDag leaf depth) paddingDepth
    value := mkConst ``encZero }
  return env.addDeclCore 0 4000 declaration none

end RCOverflow

run_meta do
  let env ← getEnv
  -- An equally shaped legal declaration must reach and pass the kernel checker.
  let controlTask ← IO.asTask
    (RCOverflow.perform env RCOverflow.controlName Level.zero RCOverflow.depth 13)
    Task.Priority.dedicated
  let .ok control := controlTask.get | throwError "positive-control task failed"
  let .ok _ := control | throwError "kernel rejected the legal positive control"
  let task ← IO.asTask
    (RCOverflow.perform env RCOverflow.candidateName (Level.param `u) RCOverflow.depth 13)
    Task.Priority.dedicated
  let .ok candidate := task.get | throwError "dedicated task failed"
  match candidate with
  | .error (.declTypeMismatch _ (.thmDecl info) _) =>
    unless info.name == RCOverflow.candidateName do
      throwError "kernel reported a type mismatch for the wrong declaration"
  | .error _ => throwError "expected the candidate's universe/type mismatch, not another kernel error"
  | .ok _ => throwError "kernel accepted the invalid polymorphic candidate"
