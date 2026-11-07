import Lean

open Lean Meta

namespace FunInfoDeps

def dependent {α : Type} (_ : Nat) (x : α) (p : α → Prop) (_ : p x) (z : α) :
    { a : α // a = z } := ⟨z, rfl⟩

def dense (n m k : Nat) (_ : n + m + k = k + m + n) : Nat := n

def assertDeps (fn : Expr) (limit : Option Nat) (back : Array (Array Nat))
    (forward : Array Bool) (result : Array Nat) : MetaM Unit := do
  let finfo ← getFunInfo fn limit
  unless finfo.paramInfo.map (·.backDeps) == back &&
      finfo.paramInfo.map (·.hasFwdDeps) == forward && finfo.resultDeps == result do
    throwError "unexpected dependencies for {fn} at arity {limit}"

def check : MetaM Unit := do
  let dep := mkConst ``dependent
  assertDeps dep none #[#[], #[], #[0], #[0], #[2, 3], #[0]]
    #[true, false, true, true, false, true] #[0, 5]
  assertDeps dep (some 3) #[#[], #[], #[0]] #[true, false, true] #[0, 2]
  assertDeps dep (some 0) #[] #[] #[]
  let partialApp := mkApp dep (mkConst ``Nat)
  assertDeps partialApp none #[#[], #[], #[], #[1, 2], #[]]
    #[false, true, true, false, true] #[4]
  assertDeps (mkConst ``dense) none #[#[], #[], #[], #[0, 1, 2]]
    #[true, true, true, false] #[]

end FunInfoDeps

run_meta FunInfoDeps.check
