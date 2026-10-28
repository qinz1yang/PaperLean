# Tests that declarations are checked by the kernel against the environment Lean checks them
# against: the messages and results are Lean 4.35.0-rc3's (the expected outputs below are official
# Lean's) for a declaration the kernel rejects, which is then an axiom that later declarations use,
# for independent declarations and ones that use earlier declarations of the module, for a structure
# (added synchronously, with constants the kernel generates) and its users, with kernel diagnostics
# on, and for declarations that use constants which rolled-back branches of the elaboration
# defined differently (the same names and type or value objects, other values or kinds; one or
# several dependencies; declarations added asynchronously and synchronously).

cat > "$TMP_DIR/KernelCheck.lean" <<'EOF'
import Lean
open Lean Elab Command Meta

-- a declaration the kernel rejects (its value does not have its type): Lean reports the kernel's
-- error and adds an axiom instead, which later declarations use
def badDecl : Declaration :=
  .thmDecl { name := `bad, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }
run_meta addDecl badDecl
theorem usesBad : 1 = 2 := (bad).elim
#print axioms usesBad

-- independent declarations, and some that use earlier ones of the module
def f (n : Nat) : Nat := n + 1
theorem f_pos (n : Nat) : 0 < f n := Nat.succ_pos n
theorem t1 : (List.range 50).length = 50 := by decide
theorem t2 : (List.range 60).length = 60 := by decide
theorem t3 : f 3 = 4 := rfl
theorem t4 (n : Nat) : 0 < f (f n) := f_pos (f n)

-- a structure (added synchronously, with constants the kernel generates) and its users
structure P where
  a : Nat
  b : Nat
def P.sum (p : P) : Nat := p.a + p.b
theorem P.sum_comm (p : P) : p.sum = p.b + p.a := Nat.add_comm _ _
theorem P.rec_use (p : P) : P.rec (motive := fun _ => Nat) (fun a b => a + b) p = p.sum := rfl

-- kernel diagnostics
set_option diagnostics true in
set_option diagnostics.threshold 0 in
theorem t5 : f (f 0) = 2 := rfl

#print axioms t4
#print axioms P.rec_use
EOF
cat > "$TMP_DIR/expected.out" <<'EOF'
KernelCheck.lean:8:0: error: (kernel) declaration type mismatch, 'bad' has type
  True
but it is expected to have type
  False
'usesBad' depends on axioms: [bad]
[diag] Diagnostics
  [type_class] used instances (max: 2, num: 2):
    [type_class] instOfNatNat ↦ 2
    [type_class] Grind.CommRing.OfCommSemiring.instOfNatQ ↦ 2
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
[diag] Diagnostics
  [reduction] unfolded declarations (max: 4, num: 2):
    [reduction] f ↦ 4
    [reduction] OfNat.ofNat ↦ 4
  [type_class] used instances (max: 2, num: 2):
    [type_class] instOfNatNat ↦ 2
    [type_class] Grind.CommRing.OfCommSemiring.instOfNatQ ↦ 2
  [kernel] unfolded declarations (max: 3, num: 7):
    [kernel] instOfNatNat ↦ 3
    [kernel] OfNat.ofNat ↦ 3
    [kernel] f ↦ 2
    [kernel] Add.add ↦ 2
    [kernel] HAdd.hAdd ↦ 2
    [kernel] instAddNat ↦ 1
    [kernel] instHAdd ↦ 1
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
't4' does not depend on any axioms
'P.rec_use' does not depend on any axioms
EOF
cd "$TMP_DIR"
capture_exit 1 lean KernelCheck.lean
$DIFF -- expected.out "$CAPTURED.out.produced" || fail "the output differs from Lean's"

cat > Rollback.lean <<'EOF'
import Lean
open Lean Elab Command Meta

-- Constants of rolled-back branches of an elaboration share their names, and their type objects,
-- with the constants of the restored environment, but not their values. Every declaration is
-- checked against the restored environment, as by Lean.

-- one dependency, defined differently on a rolled-back branch
run_meta do
  let initial ← getEnv
  let ty := mkConst ``Nat
  let mk (n : Nat) : Declaration := .defnDecl {
    name := `oneValue, levelParams := [], type := ty, value := mkNatLit n,
    hints := .abbrev, safety := .safe }
  addDecl (mk 0)
  let first ← getEnv
  setEnv initial
  addDecl (mk 1)
  setEnv first
  addDecl (.thmDecl {
    name := `oneProof, levelParams := [],
    type := mkApp3 (mkConst ``Eq [1]) ty (mkConst `oneValue) (mkNatLit 1),
    value := mkApp2 (mkConst ``Eq.refl [1]) ty (mkNatLit 1) })
theorem oneFalse : False := Nat.noConfusion oneProof
#print axioms oneFalse

-- a dependency whose value is the same object on both branches, and a constant it uses that differs
run_meta do
  let initial ← getEnv
  let ty := mkConst ``Nat
  let viaValue := mkConst `innerValue
  let inner (n : Nat) : Declaration := .defnDecl {
    name := `innerValue, levelParams := [], type := ty, value := mkNatLit n,
    hints := .abbrev, safety := .safe }
  let outer : Declaration := .defnDecl {
    name := `outerValue, levelParams := [], type := ty, value := viaValue,
    hints := .abbrev, safety := .safe }
  addDecl (inner 0); addDecl outer
  let first ← getEnv
  setEnv initial
  addDecl (inner 1); addDecl outer
  setEnv first
  addDecl (.thmDecl {
    name := `outerProof, levelParams := [],
    type := mkApp3 (mkConst ``Eq [1]) ty (mkConst `outerValue) (mkNatLit 1),
    value := mkApp2 (mkConst ``Eq.refl [1]) ty (mkNatLit 1) })
#print axioms outerProof

-- two dependencies, the latest of each added on a different branch
run_meta do
  let initial ← getEnv
  let ty := mkConst ``Nat
  let val (name : Name) (n : Nat) : Declaration := .defnDecl {
    name, levelParams := [], type := ty, value := mkNatLit n, hints := .abbrev, safety := .safe }
  addDecl (val `leftValue 0); addDecl (val `rightValue 0)
  let first ← getEnv
  setEnv initial
  addDecl (val `leftValue 1)
  let second ← getEnv
  setEnv initial
  addDecl (val `rightValue 1)
  let _ := second
  setEnv first
  let sum := mkApp2 (mkConst ``Nat.add) (mkConst `leftValue) (mkConst `rightValue)
  addDecl (.thmDecl {
    name := `twoProof, levelParams := [],
    type := mkApp3 (mkConst ``Eq [1]) ty sum (mkNatLit 2),
    value := mkApp2 (mkConst ``Eq.refl [1]) ty (mkNatLit 2) })
#print axioms twoProof

-- the same type and value objects, a definition on the rolled-back branch and opaque on the restored one
run_meta do
  let initial ← getEnv
  let ty := mkConst ``Nat
  let value := mkNatLit 0
  addDecl (.opaqueDecl {
    name := `kindValue, levelParams := [], type := ty, value := value, isUnsafe := false })
  let first ← getEnv
  setEnv initial
  addDecl (.defnDecl {
    name := `kindValue, levelParams := [], type := ty, value := value, hints := .abbrev, safety := .safe })
  setEnv first
  addDecl (.thmDecl {
    name := `kindProof, levelParams := [],
    type := mkApp3 (mkConst ``Eq [1]) ty (mkConst `kindValue) value,
    value := mkApp2 (mkConst ``Eq.refl [1]) ty value })
#print axioms kindProof

-- inductive types, which Lean adds synchronously, defined differently on two branches
run_meta do
  let initial ← getEnv
  let prop := mkSort .zero
  let ind (hyp : Expr) : Declaration := .inductDecl [] 0 [{
    name := `Both, type := prop,
    ctors := [{ name := `Both.mk, type := mkForall `h .default hyp (mkConst `Both) }] }] false
  addDecl (ind (mkConst ``False))
  let first ← getEnv
  setEnv initial
  addDecl (ind (mkConst ``True))
  setEnv first
  addDecl (.thmDecl {
    name := `bothProof, levelParams := [], type := mkConst `Both,
    value := mkApp (mkConst `Both.mk) (mkConst ``True.intro) })
theorem bothFalse : False := Both.rec (motive := fun _ => False) (fun h => h) bothProof
#print axioms bothFalse
EOF
cat > expected-rollback.out <<'EOF'
Rollback.lean:9:0: error: (kernel) declaration type mismatch, 'oneProof' has type
  1 = 1
but it is expected to have type
  oneValue = 1
'oneFalse' depends on axioms: [oneProof]
Rollback.lean:28:0: error: (kernel) declaration type mismatch, 'outerProof' has type
  1 = 1
but it is expected to have type
  outerValue = 1
'outerProof' depends on axioms: [outerProof]
Rollback.lean:50:0: error: (kernel) declaration type mismatch, 'twoProof' has type
  2 = 2
but it is expected to have type
  leftValue.add rightValue = 2
'twoProof' depends on axioms: [twoProof]
Rollback.lean:72:0: error: (kernel) declaration type mismatch, 'kindProof' has type
  0 = 0
but it is expected to have type
  kindValue = 0
'kindProof' depends on axioms: [kindProof]
Rollback.lean:90:0: error: (kernel) application type mismatch
  Both.mk True.intro
argument has type
  True
but function has type
  False → Both
'bothFalse' depends on axioms: [bothProof]
EOF
capture_exit 1 lean Rollback.lean
$DIFF -- expected-rollback.out "$CAPTURED.out.produced" || fail "the output for rolled-back constants differs from Lean's"
