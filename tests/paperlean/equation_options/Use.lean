module
public import Equations
namespace Walk
universe u
variable {α : Type u} {R : α → α → Prop}
public theorem downstream {a b : α} (p : Walk R a b)
    (h : b = a → HEq p (Walk.nil : Walk R a a) → False) :
    p.drop 0 = p.copy (Walk.getVert_zero p).symm rfl :=
  Walk.drop.eq_2 p h
end Walk
