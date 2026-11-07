module

import Lean
import Lean.Compiler.LCNF.ToDecl
public meta import Lean
meta import Lean.Compiler.LCNF.ToDecl

open Lean Compiler LCNF

-- Previously public helpers remain available to ordinary downstream imports.
def preservedMacroInline : Expr → CoreM Expr := macroInline
def preservedInlineMatchers : Expr → CoreM Expr := inlineMatchers
def preservedLCNFArg : ToLCNF.Element → ToLCNF.Element := id

@[noinline] def rightDecision (n : Nat) : Nat := dbg_trace s!"right decision {n}"; n

def shortOr (n : Nat) : Bool := decide (n = 0 ∨ rightDecision n = 5)

/--
info: right decision 1
right decision 2
---
info: [true, false, false]
-/
#guard_msgs in
#eval (List.range 3).map shortOr

-- A macro-inline definition with a dependent matcher, used both partially and over-applied.
@[macro_inline] def chooseFn (b : Bool) : Nat → Nat :=
  match b with
  | true => fun n => n + 1
  | false => fun n => n + 2

def partialChoice : Bool → Nat → Nat := chooseFn
def appliedChoice (b : Bool) (n : Nat) : Nat := chooseFn b n

def withProof (n : Nat) (_h : n = n) : Nat := appliedChoice (n == 0) n

/-- info: [1, 3, 4] -/
#guard_msgs in
#eval (List.range 3).map fun n => withProof n rfl

example : partialChoice true 9 = 10 := by native_decide
example : appliedChoice false 9 = 11 := by native_decide

-- Converting this declaration must not change the hygienic names of later declarations.
private def hygieneProbe (n : Nat) := n
run_meta do
  let before := (← getThe Core.State).nextMacroScope
  discard <| CompilerM.run (LCNF.toDecl ``hygieneProbe)
  unless (← getThe Core.State).nextMacroScope == before do
    throwError "LCNF conversion consumed an elaborator macro scope"

@[expose] public section
namespace MarkerCollision
@[macro_inline] def source (x : Nat) := x
@[noinline] def observed (x : Nat) := x
@[csimp] theorem redirect : source = observed := by funext x; rfl

elab "foreignScopeSource" : term => do
  let key := addMacroScope `MarkerCollision `_paperleanMacroBody 777
  return Expr.mdata (KVMap.empty.setNat key 0) (mkConst ``source)
@[macro_inline] def wrapper (x : Nat) := foreignScopeSource x
def first (x : Nat) := (source x, wrapper x)
def second (x : Nat) := (wrapper x, source x)

private meta def separateResults : Code .pure → Bool
  | .let d k => match d.value with
    | .const ``Prod.mk _ #[_, _, .fvar a, .fvar b] _ => a != b
    | _ => separateResults k
  | .fun _ k _ | .jp _ k => separateResults k
  | _ => false

-- Force a spelling collision while keeping the original and the exposed applications
-- in one LCNF cache. Only the original is replaced. The pair must contain both results.
private meta def check (n : Name) : CoreM Unit := withReader (fun c => {c with quotContext := `MarkerCollision}) do
  let saved := (← get).nextMacroScope
  try
    modify fun s => {s with nextMacroScope := 777}
    let decl ← CompilerM.run (LCNF.toDecl n)
    let .code c := decl.value | throwError "expected an LCNF body"
    unless separateResults c do
      throwError "foreign metadata reused an original application in {n}"
  finally
    modify fun s => {s with nextMacroScope := saved}

run_meta do
  check ``first
  check ``second
end MarkerCollision

namespace SettledEta
-- Preserve the implicit lambda when lowering this polymorphic constructor field.
structure Operations where
  empty : {α : Type} → List α
  bits : UInt32 → BitVec 32
  foldNat : {α : Type} → α → (Nat → α → α) → Nat → α

def operations : Operations := ⟨@List.nil, UInt32.toBitVec, fun {α} => @Nat.rec (fun _ => α)⟩

/-- info: ([], 5, 8) -/
#guard_msgs in
#eval (operations.empty (α := Nat), (operations.bits 5).toNat, operations.foldNat 0 (fun _ r => r + 1) 8)
-- The impossible constructors make this a valid partially applied noConfusion.
def impossible (n : Nat) : (0 = Nat.succ n) → Nat := Nat.noConfusion

end SettledEta
