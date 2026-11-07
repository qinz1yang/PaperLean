module
public import Finish
@[expose] public section
namespace V
def Arr (a b : V n) := ∀ i, a i → b i
def last (a : V (n+1)) := a .zero

def choose {n} {a b : V (n+1)} (first : Arr (drop a) (drop b))
    (last : V.last a → V.last b) : Arr a b
  | .succ i => first i
  | .zero => last

-- This uses the matcher generated for choose, including with parallel elaboration.
def chooseAgain {n} {a b : V (n+1)} (first : Arr (drop a) (drop b))
    (last : V.last a → V.last b) : Arr a b
  | .succ i => first i
  | .zero => last

def chooseRel {n} (a : V n) {β γ : Type} (r : β → γ → Prop) :
    ∀ {i}, (push a β) i → (push a γ) i → Prop
  | .succ _ => Eq
  | .zero => r
-- This constructs a constant predicate. A sort-valued result is a separate
-- control even when its alternatives are existing arguments.
def choosePred {n} (a : V n) {β : Type} (p : β → Prop) : ∀ {i}, (push a β) i → Prop
  | .succ _ => fun _ => True
  | .zero => p

def chooseType {n} (a : V n) (β : Type) : V (n+1)
  | .succ i => a i
  | .zero => β
def handler (x : Nat) : Prop := x = 0
def match_handler (x : Nat) : Prop := x = 1

def chooseGlobal {n} (f : Nat → Prop) : Ix (n+1) → Nat → Prop
  | .succ _ => handler
  | .zero => f

def chooseNamedGlobal {n} (f : Nat → Prop) : Ix (n+1) → Nat → Prop
  | .succ _ => match_handler
  | .zero => f

def chooseId {n} (f : Nat → Nat) : Ix (n+1) → Nat → Nat
  | .succ _ => @id Nat
  | .zero => f

def chooseConst {n} (f : Nat → Prop) : Ix (n+1) → Nat → Prop
  | .succ _ => Function.const Nat True
  | .zero => f

-- A local polymorphic signature may still be pending when the equation policy
-- is recorded. The same-module application stays conservative in old artifacts too.
def localId {α : Type} (x : α) := x
def chooseLocalId {n} (f : Nat → Nat) : Ix (n+1) → Nat → Nat
  | .succ _ => @localId Nat
  | .zero => f
end V
