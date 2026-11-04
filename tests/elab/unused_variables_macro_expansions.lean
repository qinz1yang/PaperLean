/-!
`linter.unusedVariables` on variables whose syntax comes from macro expansions, where the ignore
functions also apply to the expansions' outputs: several such variables in a command, nested
expansions, term macros, and variables of tactic proofs elaborated in the background.
-/

set_option linter.unusedVariables true

macro "ignoreArgs " id:declId sig:declSig : command => `(opaque $id $sig)
ignoreArgs ignored1 (x : UInt32) (y : UInt32) (z : UInt32) : UInt32

macro "wrap " c:command : command => `($c:command)
wrap ignoreArgs ignored2 (x : UInt32) (y : UInt32) : UInt32
wrap wrap ignoreArgs ignored3 (x : UInt32) : UInt32

macro "mkDef " name:ident x:ident y:ident : command => `(def $name ($x : Nat) ($y : Nat) : Nat := 0)
mkDef d1 a b
wrap mkDef d2 a b

macro "myfun " x:ident " => " b:term : term => `(fun $x => $b)
def d3 : Nat → Nat := myfun q => 0
def d4 : Nat → Nat → Nat := fun x => myfun q => 0
def d5 (a : Nat) : Nat → Nat → Nat := myfun q => myfun r => 0 + q

theorem t1 (a b : Nat) (h : a = a) : True := by
  have k : Nat := 1
  have : Nat := (myfun q => 0) 2
  exact trivial

example : (n m : Nat) → Nat → Nat := fun n m => myfun q => n
