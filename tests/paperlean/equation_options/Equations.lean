module
@[expose] public section
universe u
inductive Walk {α : Type u} (R : α → α → Prop) : α → α → Type u where
  | nil {a} : Walk R a a
  | cons {a b c} (h : R a b) (p : Walk R b c) : Walk R a c
namespace Walk
variable {α : Type u} {R : α → α → Prop}
def getVert {a b : α} : Walk R a b → Nat → α
  | .nil, _ => a
  | .cons _ _, 0 => a
  | .cons _ q, n+1 => q.getVert n
@[simp] theorem getVert_zero {a b : α} (p : Walk R a b) : p.getVert 0 = a := by cases p <;> rfl
def copy {a b a' b' : α} (p : Walk R a b) (ha : a = a') (hb : b = b') : Walk R a' b' :=
  ha ▸ hb ▸ p
set_option backward.isDefEq.respectTransparency.types false in
def drop {a b : α} (p : Walk R a b) (n : Nat) : Walk R (p.getVert n) b :=
  match p, n with
  | .nil, _ => .nil
  | q, 0 => q.copy (getVert_zero q).symm rfl
  | .cons _ q, n+1 => q.drop n
/-- Demand the equation under the caller's options before exporting it. -/
theorem requested : True := by
  have := @Walk.drop.eq_2.{0}
  trivial
end Walk
