import Lean

def _root_.Nat.mod2 : Nat → Nat
  | n+2 => n.mod2
  | n => n

protected def _root_.Nat.mod3 : Nat → Nat
  | n+2 => n.mod3
  | n => n

private def _root_.Nat.mod4 : Nat → Nat
  | n+2 => n.mod4
  | n => n

inductive Foo.Bla.T where
  | s : T → T
  | z

namespace AAA.BBB.CCC

def _root_.Foo.Bla.T.toNat₁ : Foo.Bla.T → Nat
  | .s a => a.toNat₁ + 1
  | .z => 0

protected def _root_.Foo.Bla.T.toNat₂ : Foo.Bla.T → Nat
  | .s a => a.toNat₂ + 1
  | .z => 0

private def _root_.Foo.Bla.T.toNat₃ : Foo.Bla.T → Nat
  | .s a => a.toNat₃ + 1
  | .z => 0

def _root_.Foo.Bla.T.toNat₄ : Foo.Bla.T → Nat
  | .s a => toNat₄ a + 1
  | .z => 0

protected def _root_.Foo.Bla.T.toNat₅ : Foo.Bla.T → Nat
  | .s a => T.toNat₅ a + 1
  | .z => 0

private def _root_.Foo.Bla.T.toNat₆ : Foo.Bla.T → Nat
  | .s a => toNat₆ a + 1
  | .z => 0

end AAA.BBB.CCC

-- Check both constructors, including recursive calls in all six visibility cases.
#guard Nat.mod2 7 == 1 && Nat.mod3 7 == 1 && Nat.mod4 7 == 1
#guard Foo.Bla.T.toNat₁ .z == 0 && Foo.Bla.T.toNat₁ (.s (.s .z)) == 2
#guard Foo.Bla.T.toNat₂ .z == 0 && Foo.Bla.T.toNat₂ (.s (.s .z)) == 2
#guard Foo.Bla.T.toNat₃ .z == 0 && Foo.Bla.T.toNat₃ (.s (.s .z)) == 2
#guard Foo.Bla.T.toNat₄ .z == 0 && Foo.Bla.T.toNat₄ (.s (.s .z)) == 2
#guard Foo.Bla.T.toNat₅ .z == 0 && Foo.Bla.T.toNat₅ (.s (.s .z)) == 2
#guard Foo.Bla.T.toNat₆ .z == 0 && Foo.Bla.T.toNat₆ (.s (.s .z)) == 2

open Lean in
run_meta do
  let env ← getEnv
  let expectedType ← mkArrow (mkConst ``Foo.Bla.T) (mkConst ``Nat)
  let cases := [
    (``Foo.Bla.T.toNat₁, `Foo.Bla.T.toNat₁, false, false),
    (``Foo.Bla.T.toNat₂, `Foo.Bla.T.toNat₂, false, true),
    (``Foo.Bla.T.toNat₃, `Foo.Bla.T.toNat₃, true, false),
    (``Foo.Bla.T.toNat₄, `Foo.Bla.T.toNat₄, false, false),
    (``Foo.Bla.T.toNat₅, `Foo.Bla.T.toNat₅, false, true),
    (``Foo.Bla.T.toNat₆, `Foo.Bla.T.toNat₆, true, false)]
  for (actual, user, privateDecl, protectedDecl) in cases do
    unless (← getConstInfo actual).type == expectedType do
      throwError "incorrect type for {user}"
    if privateDecl then
      unless privateToUserName? actual == some user && actual != user do
        throwError "incorrect private root name for {user}: {actual}"
    else
      unless actual == user do
        throwError "incorrect root name for {user}: {actual}"
    unless isProtected env actual == protectedDecl do
      throwError "incorrect protection for {user}"
