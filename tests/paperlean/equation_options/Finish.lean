module
@[expose] public section

inductive Ix : Nat → Type where
  | zero {n} : Ix (n + 1)
  | succ {n} : Ix n → Ix (n + 1)

def V (n : Nat) := Ix n → Type
namespace V
def drop (a : V (n+1)) : V n := fun i => a i.succ
def push (a : V n) (b : Type) : V (n+1)
  | .succ i => a i
  | .zero => b
def product : ∀ {n}, V n → V n → V n
  | 0, _, _ => fun i => nomatch i
  | n+1, a, b => push (@product n (drop a) (drop b)) (a .zero × b .zero)
def project : ∀ {n} {a b : V n} (i : Ix n), product a b i → a i
  | n+1, a, b, .succ i => @project n (drop a) (drop b) i
  | _+1, _, _, .zero => Prod.fst

-- Demand the first equation in its home module.
theorem materialized : True := by
  have := @project.eq_2
  trivial

def delayed : ∀ {n} {a b : V n} (i : Ix n), product a b i → b i
  | n+1, a, b, .succ i => @delayed n (drop a) (drop b) i
  | _+1, _, _, .zero => Prod.snd
def repeated : ∀ n, Type → V n
  | 0, _ => fun i => nomatch i
  | n+1, t => push (repeated n t) t

def captured {β} (x : β) : ∀ {n} (a : V n) (i : Ix n), a i → repeated n β i
  | n+1, a, .succ i => @captured β x n (drop a) i
  | _+1, _, .zero => fun _ => x

theorem capturedDemand : True := by
  have := @captured.eq_2
  trivial
end V
