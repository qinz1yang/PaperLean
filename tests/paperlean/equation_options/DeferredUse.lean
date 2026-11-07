module
public import Deferred

namespace Walk
universe u
variable {α : Type u} {R : α → α → Prop}

-- A producer that chooses the permissive option exports the detailed equation.
public theorem useDeferred {a b : α} (p : Walk R a b)
    (h : b = a → HEq p (Walk.nil : Walk R a a) → False) :
    p.deferred 0 = p.copy (Walk.getVert_zero p).symm rfl :=
  Walk.deferred.eq_2 p h
end Walk
