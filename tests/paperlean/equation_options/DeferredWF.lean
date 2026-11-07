module
public import Equations

@[expose] public section
namespace Walk
universe u
variable {α : Type u} {R : α → α → Prop}

-- No transparency override at this definition, and no request for its generated equations.
def deferred {a b : α} (p : Walk R a b) (n : Nat) : Walk R (p.getVert n) b :=
  match p, n with
  | .nil, _ => .nil
  | q, 0 => q.copy (getVert_zero q).symm rfl
  | .cons _ q, n+1 => q.deferred n
termination_by n
end Walk
