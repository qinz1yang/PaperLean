import Lean.Elab.Command

/-!
`linter.constructorNameAsVariable` on binders of types that are and are not in weak head normal form
when the linter runs: applications of an inductive type with parameters, types that unfold to one,
types with metavariables when the binder is elaborated, local variables with and without a value,
pi types, sorts, pattern variables and structure fields.
-/

set_option linter.unusedVariables false

-- The test harness passes `-Dlinter.all=false`, which would disable this linter.
open Lean Elab Command in
elab "unset_option " opt:ident : command => do
  modifyScope fun scope => { scope with opts := scope.opts.erase opt.getId.eraseMacroScopes }

unset_option linter.all

inductive B (α : Type) where
  | x | y (a : α) | z

def f1 (x : B Nat) (y : B Nat) (z : B Nat) : Unit := ()

abbrev C := B Nat
def f2 (x : C) : Unit := ()

def D := B Nat
def f3 (z : D) : Unit := ()

def f4 : B Nat → Unit := fun x => ()

def f5 := fun (x : _) => (x : B Nat)

def f6 (x : B Nat → B Nat) (z : Type) (y : Prop) : Unit := ()

def f7 : B Nat → B Bool → Unit
  | x, z => ()

def f8 (a : B Nat) : Unit :=
  match a with
  | x => ()

theorem t1 (x : B Nat) (h : x = x) : True := trivial

def f9 (x : Nat) (z : Option (B Nat)) (none : Option Nat) : Unit := ()

structure S where
  x : B Nat

def f10 (α : Type) (x : α) (z : List α) : Unit := ()

def f11 : Unit :=
  let α := B Nat
  let g := fun (x : α) (z : α → α) => ()
  g .x id

def f12 (F : Type → Type) (x : F Nat) : Unit := ()
