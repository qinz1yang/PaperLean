module
@[expose] public section
universe u

namespace ProofBase
abbrev operation {α : Type u} (x : α) (n : Nat) := (x,n)
def wrapper {α : Type u} (x : α) (n : Nat) := operation x (id n)
def source {α : Type u} (x : α) (n : Nat) := (operation x n, operation x (n+1))
def target {α : Type u} (x : α) (n : Nat) := (wrapper x n, wrapper x (n+1))
def single {α : Type u} (x : α) (n : Nat) := (wrapper x n, operation x (n+1))

inductive Holds {α : Type u} (x : α) : Prop where
  | intro : Holds x
theorem witness {α : Type u} (x : α) (n : Nat) : Holds (source x n) := .intro
theorem witnessEq {α : Type u} (x : α) (n : Nat) : source x n = source x n := rfl

-- Generalizing this shared head is invalid: it erases its second argument,
-- whereas a locally bound function can distinguish n from n+1.
abbrev ignoreArg {α : Type u} (x : α) (_n : Nat) := x
def shifted {α : Type u} (x : α) (n : Nat) := ignoreArg x (n+1)
def ignoreSource {α : Type u} (x : α) (n : Nat) := (ignoreArg x n, ignoreArg x (n+1))
def ignoreTarget {α : Type u} (x : α) (n : Nat) := (shifted x n, shifted x (n+1))
theorem ignoreWitness {α : Type u} (x : α) (n : Nat) : Holds (ignoreSource x n) := .intro
-- A dependency may have its own sorry. Users of its public API should not get
-- a new direct sorry diagnostic when their theorem bodies are generated.
def keep (n : Nat) (_ : Nat) := n
set_option warn.sorry false in
def sorryWrapper {α : Type u} (x : α) (n : Nat) := operation x (keep n (by sorry))
def sorryTarget {α : Type u} (x : α) (n : Nat) :=
  (sorryWrapper x n, sorryWrapper x (n+1))
end ProofBase
