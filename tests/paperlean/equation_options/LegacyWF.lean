module
public import Equations
@[expose] public section
namespace Walk
universe u
variable {α : Type u} {R : α → α → Prop}

-- Stock saves useBackward here, while the local transparency choice stays absent.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
def legacyWF {a b : α} (p : Walk R a b) (n : Nat) : Walk R (p.getVert n) b :=
  match p, n with
  | .nil, _ => .nil
  | q, 0 => q.copy (getVert_zero q).symm rfl
  | .cons _ q, n+1 => q.legacyWF n
termination_by n
end Walk
