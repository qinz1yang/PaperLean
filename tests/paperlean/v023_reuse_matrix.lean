import Lean

-- Repeated synchronous builtin commands populate and then reuse across commands.
#synth BEq (List (Option (Nat × Nat)))
#synth BEq (List (Option (Nat × Nat)))
#synth BEq (List (Option (Nat × Nat)))
#synth BEq (List (Option (Nat × Nat)))
#synth BEq (List (Option (Nat × Nat)))
#synth BEq (List (Option (Nat × Nat)))
#synth BEq (List (Option (Nat × Nat)))
#synth BEq (List (Option (Nat × Nat)))
#synth BEq (List (Option (Nat × Nat)))
#synth BEq (List (Option (Nat × Nat)))
#synth BEq (List (Option (Nat × Nat)))
#synth BEq (List (Option (Nat × Nat)))

namespace V023Matrix
class Tag (α : Type) where
  value : Nat
instance baseTag : Tag Nat := ⟨10⟩
#synth Tag Nat
#synth Tag Nat
#synth Tag Nat
#synth Tag Nat
#synth Tag Nat
#synth Tag Nat
#synth Tag Nat
#synth Tag Nat
#synth Tag Nat
#synth Tag Nat
#guard (inferInstance : Tag Nat).value == 10

section
local instance (priority := 2000) changedTag : Tag Nat := ⟨20⟩
#synth Tag Nat
#synth Tag Nat
#synth Tag Nat
#synth Tag Nat
#synth Tag Nat
#synth Tag Nat
#synth Tag Nat
#synth Tag Nat
#guard (inferInstance : Tag Nat).value == 20
end
#synth Tag Nat
#synth Tag Nat
#synth Tag Nat
#synth Tag Nat
#synth Tag Nat
#synth Tag Nat
#synth Tag Nat
#synth Tag Nat
#guard (inferInstance : Tag Nat).value == 10

section
variable {α : Type} [BEq α]
def localHeader0 (xs : List (Option α)) : Bool := xs == xs
def localHeader1 (xs : List (Option α)) : Bool := xs == xs
def localHeader2 (xs : List (Option α)) : Bool := xs == xs
def localHeader3 (xs : List (Option α)) : Bool := xs == xs
def localHeader4 (xs : List (Option α)) : Bool := xs == xs
def localHeader5 (xs : List (Option α)) : Bool := xs == xs
def localHeader6 (xs : List (Option α)) : Bool := xs == xs
def localHeader7 (xs : List (Option α)) : Bool := xs == xs
end

theorem checked (n : Nat) : n + 0 = n := Nat.add_zero n
#print axioms checked
end V023Matrix
