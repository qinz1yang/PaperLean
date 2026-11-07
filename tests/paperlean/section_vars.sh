# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests the reuse of section variables (`Lean.PaperLean.SectionVars`): the output is Lean
# 4.35.0-rc3's (the expected outputs below are official Lean's) for declarations that use the
# variables of earlier ones, also with `include` and `variable ... in`; for a namespace in which the
# type of a variable means another constant, and for an `open` and an `export` after which it is
# ambiguous, where the recorded name resolution no longer holds and the variables are elaborated
# again; for instances, whose header is elaborated twice; for binders whose elaboration records a
# module use (`Lean.ExtraModUses`); for variables whose kinds or local instances, or the classes of
# whose types, change; for binders of user elaborators, which are reused, but for those that start a
# task; and after instances and macros are added. Every reuse is also compared with Lean's
# elaboration (`PAPERLEAN_REUSE_ORACLE`), and `PAPERLEAN_EXACT` reuses nothing. Also that later
# metavariables are numbered as in Lean's elaboration; that the declarations of a module whose
# commands reuse variables with names with macro scopes (instance binders, arrows, binders of
# macros) are Lean's (the `.olean` is the one of a run that reuses nothing); that variables are
# reused with auto-bound implicits; that the oracle reports a wrong entry of Lean's caches in a reuse
# and fails the run (a fault put in on purpose, `PAPERLEAN_REUSE_FAULT`, which applies only where the
# oracle runs); that a further frontend in the process turns reuse and the oracle off, with a
# message; that variables elaborated with info trees off are not reused with them on, nor the other
# way round; that the oracle compares with an elaboration that reuses no typeclass results; and that
# a reuse renames the binder names of the quotation context in the keys of Lean's `funInfo` cache,
# which the oracle compares with their binder names.

export PAPERLEAN_REUSE=1

cat > "$TMP_DIR/SectionVars.lean" <<'EOF'
universe u

class C (α : Type u) where
  x : α

namespace A
def T := Int
end A
def T := Nat

section basic
variable {α : Type u} [C α] (a b : α) (h : a = b)

include h in
theorem t1 : b = a := h.symm
theorem t2 : a = a := rfl
def f : α := C.x
theorem t3 : f = (C.x : α) := rfl
variable (c : α) in
theorem t4 : c = c := rfl
theorem t5 (k : Nat) : a = a ∧ k = k := ⟨rfl, rfl⟩
#check @t1
#check @f
#check @t4
#check @t5
end basic

section shadow
variable (n : T)
theorem s1 : n = n := rfl
namespace A
-- here `T` is `A.T`, and Lean elaborates the variable again as `A.T`
theorem s2 : n = n := rfl
end A
#check @s1
#check @A.s2
end shadow

section ambiguous
variable (m : T)
theorem u1 : m = m := rfl
open A
-- here `T` is ambiguous, so Lean's elaboration of the variable fails
theorem u2 : m = m := rfl
end ambiguous

section alias
variable (m : T)
theorem v1 : m = m := rfl
export A (T)
-- here `T` is ambiguous too (it is also an alias of `A.T`), in the same namespace and with the same
-- open declarations
theorem v2 : m = m := rfl
end alias

section instances
class D (α : Type u) where
  d : α
variable {α : Type u} {β : Type u} [C α] (a : α)
-- the instance's header is elaborated twice (naming it restores the state), and its binder `β`
-- has the name of a section variable
instance (β : Type u) [C β] : D (α × β) := ⟨(C.x, C.x)⟩
theorem i1 [C β] : (D.d : α × β) = (C.x, C.x) := rfl
instance : D α := ⟨C.x⟩
theorem i2 : (D.d : α) = C.x := rfl
#check @i1
#check @i2
end instances
EOF
cat > "$TMP_DIR/expected.out" <<'EOF'
SectionVars.lean:15:0: warning: automatically included section variable(s) unused in theorem `t1`:
  [C α]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [C α] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
SectionVars.lean:16:0: warning: automatically included section variable(s) unused in theorem `t2`:
  [C α]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [C α] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
SectionVars.lean:20:0: warning: automatically included section variable(s) unused in theorem `t4`:
  [C α]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [C α] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
SectionVars.lean:21:0: warning: automatically included section variable(s) unused in theorem `t5`:
  [C α]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [C α] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
@t1 : ∀ {α : Type u_1} [C α] (a b : α), a = b → b = a
@f : {α : Type u_1} → [C α] → α
@t4 : ∀ {α : Type u_1} [C α] (c : α), c = c
@t5 : ∀ {α : Type u_1} [C α] (a : α) (k : Nat), a = a ∧ k = k
s1 : ∀ (n : T), n = n
A.s2 : ∀ (n : A.T), n = n
SectionVars.lean:44:8: warning: declaration uses `sorry`
SectionVars.lean:53:8: warning: declaration uses `sorry`
@i1 : ∀ {α β : Type u_1} [inst : C α] [inst_1 : C β], D.d = (C.x, C.x)
@i2 : ∀ {α : Type u_1} [inst : C α], D.d = C.x
EOF
cd "$TMP_DIR"
capture_exit 0 lean SectionVars.lean
$DIFF -- expected.out "$CAPTURED.out.produced" || fail "the output differs from Lean's"
# every reuse agrees with Lean's elaboration
PAPERLEAN_REUSE_ORACLE=1 lean SectionVars.lean > run.out 2>&1 || fail "lean failed: $(cat run.out)"
$DIFF -- expected.out run.out || fail "the output with the oracle differs from Lean's"
# the variables were reused, and elaborated again where the name resolution changed
{ echo "import Lean"; cat SectionVars.lean; echo 'run_cmd do let (r, n, f) ← Lean.PaperLean.SectionVars.stats; Lean.logInfo m!"reused {r}, elaborated {n}, of them after a change {f}"'; } > Stats.lean
lean Stats.lean > stats.out 2>&1
R=$(sed -n 's/.*reused \([0-9]*\), elaborated \([0-9]*\), of them after a change \([0-9]*\).*/\1 \3/p' stats.out)
set -- $R
[ -n "${1:-}" ] && [ "$1" -ge 6 ] || fail "too few reuses: $(tail -2 stats.out)"
[ "${2:-0}" -ge 3 ] || fail "the changed name resolutions were not noticed: $(tail -2 stats.out)"
# `PAPERLEAN_EXACT` reuses nothing
PAPERLEAN_EXACT=1 lean Stats.lean > exact.out 2>&1
grep -q "reused 0," exact.out || fail "the exact run reused: $(grep reused exact.out)"
# binders whose elaboration records a module use (the macro of the notation `×`, from
# `Init.Notation`): the module uses are Lean's (the expected outputs are official Lean's). Naming an
# anonymous instance elaborates the variables and then restores the state, dropping the module use
# that this first elaboration in a public scope records; the instance's own elaboration records it
# again (in `NoUses`, without `×`, nothing else records it).
for v in Uses NoUses; do
  if [ $v = Uses ]; then ty="Nat × Nat"; else ty="Prod Nat Nat"; fi
  printf 'module\npublic section\nvariable (p : %s)\ninstance : Inhabited Nat := ⟨0⟩\n' "$ty" > $v.lean
  cat > Read$v.lean <<EOF2
import Lean
import $v
open Lean in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? \`$v | throwError "no module $v"
  let uses := (getExtraModUses env idx).map fun u => s!"{u.module} {u.isExported} {u.isMeta}"
  logInfo m!"{uses.qsort (· < ·) |>.toList}"
EOF2
  mkdir -p lib
  lean --root=. -o lib/$v.olean $v.lean > uses.out 2>&1 ||
    fail "$v.lean failed: $(cat uses.out)"
  LEAN_PATH=lib lean Read$v.lean > read_uses.out 2>&1 || fail "Read$v.lean failed: $(cat read_uses.out)"
  if [ $v = Uses ]; then
    echo "[Init.Notation false false, Init.Notation true false, Init.Prelude true false]"
  else
    echo "[Init.Prelude true false]"
  fi | $DIFF -- - read_uses.out || fail "the module uses of $v differ from Lean's"
done
# binders that an elaborator that is not on the whitelist elaborates are not reused
cat > UserElab.lean <<'EOF2'
import Lean
open Lean Elab Term
elab "natType%" : term => return mkConst ``Nat
variable (n : natType%)
theorem e1 : n = n := rfl
theorem e2 : n = n := rfl
theorem e3 : n + 0 = n := rfl
EOF2
PAPERLEAN_REUSE_STATS=user_elab.stats lean UserElab.lean > user_elab.out 2>&1 ||
  fail "UserElab.lean failed: $(cat user_elab.out)"
awk -F '\t' '$1 == "UserElab.lean" && $6 == 0 && $7 == 3' user_elab.stats | grep -q . ||
  fail "binders of a user elaborator were reused: $(cat user_elab.stats)"
grep -q "NatType.*not on the whitelist=3@" user_elab.stats ||
  fail "UserElab.lean does not say why: $(cat user_elab.stats)"
# binders with a numeral (`2 ^ n`, whose default instances are tried) are reused
cat > Numeral.lean <<'EOF2'
import Lean
variable (n : Nat) (h : 2 ^ n < 10)
include h
theorem t1 : True := trivial
theorem t2 : True := trivial
theorem t3 : True := trivial
EOF2
PAPERLEAN_REUSE_STATS=numeral.stats lean Numeral.lean > numeral.out 2>&1 ||
  fail "Numeral.lean failed: $(cat numeral.out)"
awk -F '\t' '$1 == "Numeral.lean" && $6 >= 2' numeral.stats | grep -q . ||
  fail "binders with a numeral were not reused: $(cat numeral.stats)"
# an elaborator that starts a task makes the elaboration unusable: the task's work is not recorded
cat > Task.lean <<'EOF2'
import Lean.Elab.ElabRules
open Lean Elab Term
elab "taskNat%" : term => return (Task.spawn fun _ => Lean.mkConst ``Nat).get
variable (n : taskNat%)
theorem e1 : n = n := rfl
theorem e2 : n = n := rfl
theorem e3 : n + 0 = n := rfl
EOF2
PAPERLEAN_DEBUG_REUSE=1 PAPERLEAN_REUSE_STATS=task.stats lean Task.lean > task.out 2>&1 ||
  fail "Task.lean failed: $(cat task.out)"
grep -q "section variables not kept: not recordable: .*a task" task.out ||
  fail "the task was not noticed: $(cat task.out)"
awk -F '\t' '$1 == "Task.lean" && $6 == 0' task.stats | grep -q . ||
  fail "section variables whose elaborator starts a task were reused: $(cat task.stats)"
# the variables have the kinds and local instances that Lean's elaboration gives them: a `__`
# variable is an implementation detail; a variable whose type is not known yet when Lean adds it is
# no local instance
cat > Kinds.lean <<'EOF2'
variable (__h : 2 = 2)
include __h
theorem t1 : True := trivial
example : 2 = 2 := by assumption
EOF2
lean Kinds.lean > kinds.out 2>&1 && fail "an implementation-detail variable became visible"
grep -q "assumption" kinds.out || fail "Kinds.lean failed otherwise than in Lean: $(cat kinds.out)"
cat > Insts.lean <<'EOF2'
class Foo : Prop where
variable (inst : _) (h : @Eq Foo inst inst)
include inst h
theorem t0 : True := trivial
example : Foo := inferInstance
EOF2
lean Insts.lean > insts.out 2>&1 && fail "a variable became a local instance"
grep -q "failed to synthesize" insts.out || fail "Insts.lean failed otherwise than in Lean: $(cat insts.out)"
# an elaborator that reads a file: the variables of `t1` see the file as it is then
cat > ReadsFile.lean <<'EOF2'
import Lean.Elab.ElabRules
open Lean Elab Term
elab "flag%" : term => do
  let s ← IO.FS.readFile "flag.txt"
  return if s == "1" then mkConst ``True else mkConst ``False
#eval IO.FS.writeFile "flag.txt" "1"
variable (h : flag%)
include h
theorem t0 : True := trivial
#eval IO.FS.writeFile "flag.txt" "0"
theorem t1 : True := h
EOF2
lean ReadsFile.lean > reads_file.out 2>&1 && fail "the variables of t1 saw the file as it was"
grep -q "Type mismatch" reads_file.out || fail "ReadsFile.lean failed otherwise than in Lean: $(cat reads_file.out)"
# a type that becomes a class after the variables were first elaborated: Lean adds `x` before its
# type is known, so `x` is no local instance (the expected output is official Lean's)
cat > LateClass.lean <<'EOF2'
structure D : Prop where
variable (F : D → Prop) (x : _) (h : F x)
include F x h
theorem t0 : True := trivial
attribute [class] D
theorem t1 : D := inferInstance
EOF2
cat > late_class.expected <<'EOF2'
LateClass.lean:4:0: warning: automatically included section variable(s) unused in theorem `t0`:
  h
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit h in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
LateClass.lean:6:18: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  D

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
EOF2
lean LateClass.lean > late_class.out 2>&1 && fail "a variable became a local instance that Lean's is not"
$DIFF -- late_class.expected late_class.out || fail "LateClass.lean: the output differs from Lean's"
cat > LateInst.lean <<'EOF2'
set_option checkBinderAnnotations false
structure E : Prop where
variable (F : E → Prop) [x : _] (h : F x)
include F x h
theorem t0 : True := trivial
attribute [class] E
theorem t1 : E := inferInstance
theorem t2 : E := inferInstance
EOF2
cat > late_inst.expected <<'EOF2'
LateInst.lean:5:0: warning: automatically included section variable(s) unused in theorem `t0`:
  h
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit h in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
LateInst.lean:7:18: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  E

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
LateInst.lean:8:18: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  E

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
EOF2
lean LateInst.lean > late_inst.out 2>&1 && fail "an instance-implicit variable became a local instance that Lean's is not"
$DIFF -- late_inst.expected late_inst.out || fail "LateInst.lean: the output differs from Lean's"
# later metavariables are numbered as in Lean's elaboration, which made some for the variables, also
# in a command that reuses them: the second `#check` reuses those of the first (the expected output is
# official Lean's)
cat > Mvars.lean <<'EOF2'
section
variable {α : Type} (a b : α) (h : a = b)
include h
theorem t1 : b = a := h.symm
#check fun x => x
#check fun x y => x y
end
EOF2
cat > mvars.expected <<'EOF2'
fun x => x : ?m.2 → ?m.2
Mvars.lean:6:18: error: Function expected at
  x
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  y
fun x y => ?m.5 : (x : ?m.2) → (y : ?m.6 x) → ?m.7 x y
EOF2
lean Mvars.lean > mvars.out 2>&1 && fail "Mvars.lean did not fail as in Lean"
$DIFF -- mvars.expected mvars.out || fail "metavariables are numbered otherwise than in Lean"
{ echo "import Lean"; cat Mvars.lean; echo 'run_cmd do let (r, _, _) ← Lean.PaperLean.SectionVars.stats; Lean.logInfo m!"reused {r}"'; } > MvarsStats.lean
lean MvarsStats.lean > mvars_stats.out 2>&1 || true
grep -q "reused [1-9]" mvars_stats.out || fail "Mvars.lean reused nothing: $(tail -2 mvars_stats.out)"
# the elaboration of the variables after instances of their classes and macros of their syntax kinds
# are added, and the typeclass results reused across these changes (the expected output is official
# Lean's)
cat > Deps.lean <<'EOF2'
class Base (α : Type) where
  b : α
class Dep (α : Type) [Base α] where
  d : α
notation "MyT" => Nat
section
variable {α : Type} [Base α] [Dep α] (n : MyT)
theorem s1 : (Dep.d : α) = Dep.d ∧ n = n := ⟨rfl, rfl⟩
-- an instance of another class and a macro of another syntax kind
instance : Inhabited (Fin 3 → Nat) := ⟨fun _ => 0⟩
macro "other%" : term => `(0)
theorem s2 : (Dep.d : α) = Dep.d ∧ n = n := ⟨rfl, rfl⟩
theorem s3 : (Dep.d : α) = Dep.d ∧ n = n := ⟨rfl, rfl⟩
-- an instance of a class that the elaboration of the variables used
instance : Base Nat := ⟨0⟩
theorem s4 : (Dep.d : α) = Dep.d ∧ n = n := ⟨rfl, rfl⟩
theorem s5 : (Dep.d : α) = Dep.d ∧ n = n := ⟨rfl, rfl⟩
-- a macro of the syntax kind of a variable's type, which gives another type
macro_rules | `(MyT) => `(Int)
theorem s6 : (Dep.d : α) = Dep.d ∧ n = n := ⟨rfl, rfl⟩
#check @s5
#check @s6
end
EOF2
cat > deps.expected <<'EOF2'
@s5 : ∀ {α : Type} [inst : Base α] [inst_1 : Dep α] (n : MyT), Dep.d = Dep.d ∧ n = n
@s6 : ∀ {α : Type} [inst : Base α] [inst_1 : Dep α] (n : Int), Dep.d = Dep.d ∧ n = n
EOF2
lean Deps.lean > deps.out 2>&1 || fail "Deps.lean failed: $(cat deps.out)"
$DIFF -- deps.expected deps.out || fail "Deps.lean: the output differs from Lean's"
PAPERLEAN_REUSE_ORACLE=1 lean Deps.lean > deps_oracle.out 2>&1 ||
  fail "Deps.lean failed with the oracle: $(cat deps_oracle.out)"
{ echo "import Lean"; cat Deps.lean; echo 'run_cmd do let (r, n, f) ← Lean.PaperLean.SectionVars.stats; Lean.logInfo m!"reused {r}, elaborated {n}, of them after a change {f}"'; } > DepsStats.lean
lean DepsStats.lean > deps_stats.out 2>&1
R=$(sed -n 's/.*reused \([0-9]*\), elaborated \([0-9]*\), of them after a change \([0-9]*\).*/\1 \3/p' deps_stats.out)
set -- $R
[ -n "${1:-}" ] && [ "$1" -ge 3 ] || fail "too few reuses: $(tail -2 deps_stats.out)"
[ "${2:-0}" -ge 2 ] || fail "the changes of instances and macros were not noticed: $(tail -2 deps_stats.out)"
# variables whose names and types have names with macro scopes (an instance binder, an arrow, the
# binder of a macro, an inaccessible binder): the declarations are Lean's, also in their binder names
# (the module is the one of a run that reuses nothing)
cat > Hygiene.lean <<'EOF2'
class C (α : Type) where
  c : α → α
notation "Fn" α => ∀ (_ : α), α
variable {α : Type} [C α] [Inhabited α] (f : α → α) (g : Fn α) (p : ∀ x ∈ [f], x = x) (_ : f = g)
include f g p
theorem h1 : C.c (f (g default)) = C.c (f (g default)) := rfl
theorem h2 : C.c (f (g default)) = C.c (f (g default)) := rfl
def h3 : α := C.c (f (g default))
theorem h4 : True := trivial
EOF2
mkdir -p hyg
PAPERLEAN_REUSE_STATS=hyg.stats lean -o hyg/reuse.olean Hygiene.lean > hyg.out 2>&1 ||
  fail "Hygiene.lean failed: $(cat hyg.out)"
PAPERLEAN_EXACT=1 lean -o hyg/exact.olean Hygiene.lean > hyg_exact.out 2>&1 ||
  fail "Hygiene.lean failed without reuse: $(cat hyg_exact.out)"
awk -F '\t' '$1 == "Hygiene.lean" && $6 >= 3' hyg.stats | grep -q . ||
  fail "Hygiene.lean reused too few elaborations: $(cat hyg.stats)"
cmp -s hyg/reuse.olean hyg/exact.olean || fail "the declarations of Hygiene.lean differ from Lean's"
$DIFF -- hyg_exact.out hyg.out || fail "the output of Hygiene.lean differs from Lean's"
# with auto-bound implicits (whose elaboration retries with each auto-bound variable)
cat > Auto.lean <<'EOF2'
set_option autoImplicit true
variable (x : α) (y : β) (h : HEq x y)
include h
theorem a1 : HEq x y := h
theorem a2 : HEq y x := h.symm
theorem a3 : True := trivial
#check @a2
EOF2
PAPERLEAN_REUSE_STATS=auto.stats lean Auto.lean > auto.out 2>&1 || fail "Auto.lean failed: $(cat auto.out)"
PAPERLEAN_EXACT=1 lean Auto.lean > auto_exact.out 2>&1
$DIFF -- auto_exact.out auto.out || fail "the output of Auto.lean differs from Lean's"
grep -q "@a2 : ∀ {α β : Sort u_1} (x : α) (y : β), x ≍ y → y ≍ x" auto.out ||
  fail "Auto.lean does not test what it should: $(cat auto.out)"
awk -F '\t' '$1 == "Auto.lean" && $6 >= 2' auto.stats | grep -q . ||
  fail "variables with auto-bound implicits were not reused: $(cat auto.stats)"
# the oracle checks every entry of Lean's caches that a reuse sets: with a fault put in on purpose
# (`PAPERLEAN_REUSE_FAULT=stale-cache` keeps an entry of the `inferType` cache under its key from
# before the renaming, the defect that `CacheProbe` of `reuse_exact.sh` covers), the second probe
# would find an entry that `inferType` does not compute: the oracle reports it and `lean` fails
cat > Stale.lean <<'EOF2'
import Lean
open Lean Elab Term Meta Command
elab "probe" : command => runTermElabM fun _ => do
  let mut bad : Nat := 0
  for (k, v) in (← getThe Meta.State).cache.inferType do
    let fresh ← (show MetaM Expr from
      withReader (fun ctx => { ctx with cacheInferType := false }) (inferType k.expr))
    unless v.equal fresh do bad := bad + 1
  logInfo m!"wrong entries: {bad}"
set_option quotPrecheck false in
notation "Fn" => ∀ (_ : Nat), Nat
variable (f : Fn) (h : (fun (_ : Nat) => f) 0 = f)
probe
probe
EOF2
PAPERLEAN_REUSE_FAULT=stale-cache lean Stale.lean > stale.out 2>&1
[ "$(grep -c "wrong entries: 0" stale.out)" = 2 ] ||
  fail "a fault was put in without the oracle: $(cat stale.out)"
PAPERLEAN_EXACT=1 lean Stale.lean > stale_exact.out 2>&1
[ "$(grep -c "wrong entries: 0" stale_exact.out)" = 2 ] ||
  fail "Stale.lean does not test what it should: $(cat stale_exact.out)"
oracle_fails() {
  local fault=$1 what=$2 f=$3 r=0
  PAPERLEAN_REUSE_FAULT=$fault PAPERLEAN_REUSE_ORACLE=1 lean $f > oracle_fault.out 2> oracle_fault.err || r=$?
  [ $r != 0 ] || fail "$f: the oracle let a wrong entry pass: $(cat oracle_fault.out)"
  grep -q "PaperLean: the reuse oracle found a difference: section variables: elaborated differently ($what" oracle_fault.err ||
    fail "$f: the oracle did not say what differs: $(cat oracle_fault.err)"
  ! grep -q "wrong entries: 1" oracle_fault.out || fail "$f: a wrong entry was observed: $(cat oracle_fault.out)"
}
oracle_fails stale-cache "an entry of the cache of .inferType. that Lean's elaboration does not make" Stale.lean
# a frontend that a program starts after the module's elaboration, the second of the process: nothing
# is reused and no oracle or fault applies from there on, which `lean` says, and its output is Lean's
cat > Driver.lean <<'EOF2'
import Lean
/-! Test a frontend started after command-line elaboration ends. -/
open Lean Elab
unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let input ← IO.FS.readFile "Stale.lean"
  let opts := Options.empty.setBool `internal.cmdlineSnapshots true
  discard <| runFrontend input opts "<inner>" `Inner
EOF2
PAPERLEAN_EXACT=1 lean --run Driver.lean > driver_exact.out 2>&1 ||
  fail "Driver.lean failed: $(cat driver_exact.out)"
[ "$(grep -c "wrong entries: 0" driver_exact.out)" = 2 ] ||
  fail "Driver.lean does not test what it should: $(cat driver_exact.out)"
PAPERLEAN_REUSE_FAULT=stale-cache PAPERLEAN_REUSE_ORACLE=1 lean --run Driver.lean \
  > driver.out 2> driver.err || fail "Driver.lean failed: $(cat driver.out driver.err)"
$DIFF -- driver_exact.out driver.out || fail "the output of a further frontend differs from Lean's"
grep -q "PaperLean: a further frontend in this process (<inner>): reuse of results and its oracle are off from here on" driver.err ||
  fail "a further frontend did not say that reuse is off: $(cat driver.err)"
# variables elaborated with info trees off are not reused with them on, nor the other way round
# (the fresh names may differ, which `P` drops); the oracle finds no difference
cat > InfoEnabled.lean <<'EOF2'
import Lean
open Lean Elab Command
elab "noinfo " c:command : command => withEnableInfoTree false (elabCommand c)
section
variable (n : Nat)
noinfo theorem t0 : n = n := rfl
#info_trees in
theorem t1 : n = n := rfl
end
section
variable (m : Nat)
#info_trees in
theorem t2 : m = m := rfl
noinfo theorem t3 : m = m := rfl
#info_trees in
theorem t4 : m = m := rfl
end
EOF2
P='s/_uniq\.[0-9]*/_uniq/g'
PAPERLEAN_REUSE_STATS=info.stats lean InfoEnabled.lean 2>&1 | sed "$P" > info.out
PAPERLEAN_EXACT=1 lean InfoEnabled.lean 2>&1 | sed "$P" > info_exact.out
[ "$(grep -c "isBinder := true" info_exact.out)" -ge 3 ] ||
  fail "InfoEnabled.lean does not test what it should: $(cat info_exact.out)"
$DIFF -- info_exact.out info.out || fail "variables were reused across the enabling of info trees"
awk -F '\t' '$1 == "InfoEnabled.lean" && $6 >= 1' info.stats | grep -q . ||
  fail "InfoEnabled.lean reused nothing: $(cat info.stats)"
PAPERLEAN_REUSE_ORACLE=1 lean InfoEnabled.lean > info_oracle.out 2>&1 ||
  fail "InfoEnabled.lean failed with the oracle: $(cat info_oracle.out)"
# the oracle's own elaboration reuses no typeclass results: as many are reused as without the oracle,
# where the variables' searches are not made again
cat > OracleTc.lean <<'EOF2'
class C (α : Type) where
  x : α
instance : C Nat := ⟨0⟩
variable (n : Fin (C.x (α := Nat) + 1))
theorem t1 : n = n := rfl
theorem t2 : n = n := rfl
theorem t3 : n = n := rfl
theorem t4 : n = n := rfl
EOF2
PAPERLEAN_REUSE_STATS=otc.stats lean OracleTc.lean > /dev/null
PAPERLEAN_REUSE_ORACLE=1 PAPERLEAN_REUSE_STATS=otc_oracle.stats lean OracleTc.lean > /dev/null
awk -F '\t' '$6 >= 3' otc.stats | grep -q . || fail "OracleTc.lean reused too little: $(cat otc.stats)"
[ "$(cut -f2 otc.stats)" = "$(cut -f2 otc_oracle.stats)" ] ||
  fail "the oracle's elaboration reused typeclass results: $(cat otc.stats otc_oracle.stats)"
# the keys of Lean's `funInfo` cache have the binder names of their quotation context, here of the
# head of `isDefEq`'s arguments, a projection of a term with a macro's binders, which `getFunInfo`
# caches: the probes print those of their own commands (with constants that are imported: the
# realization of a local constant's `funInfo` starts a task). The oracle compares the binder names
# of these keys, which the cache does not: with the fault it reports a key that keeps the names of
# the recording.
cat > FunInfoLib.lean <<'EOF2'
structure S where
  f : Nat → Type
axiom mk (g : Nat → Nat) : S
macro "m%" : term => `(mk (fun z => z))
EOF2
lean -o FunInfoLib.olean FunInfoLib.lean || fail "FunInfoLib.lean failed"
cat > FunInfoKey.lean <<'EOF2'
import Lean
import FunInfoLib
open Lean Elab Command
partial def binders : Expr → List Name
  | .lam n t b _ => n :: binders t ++ binders b
  | .app f a => binders f ++ binders a
  | .proj _ _ b => binders b
  | _ => []
elab "probe" : command => runTermElabM fun _ => do
  let mut names := #[]
  for (k, _) in (← getThe Meta.State).cache.funInfo do
    names := names ++ (binders k.expr).toArray
  logInfo m!"funInfo binders: {names.map (·.toString)}"
variable (x : (m%).f 1) (h : @id ((m%).f (0 + 1)) x = x)
probe
probe
probe
EOF2
LEAN_PATH=. PAPERLEAN_REUSE_STATS=fun_info.stats lean FunInfoKey.lean > fun_info.out 2>&1 ||
  fail "FunInfoKey.lean failed: $(cat fun_info.out)"
LEAN_PATH=. PAPERLEAN_EXACT=1 lean FunInfoKey.lean > fun_info_exact.out 2>&1
[ "$(grep -c "_hygCtx" fun_info_exact.out)" = 3 ] &&
  [ "$(grep "_hygCtx" fun_info_exact.out | sort -u | wc -l)" -eq 3 ] ||
  fail "FunInfoKey.lean does not test what it should: $(cat fun_info_exact.out)"
awk -F '\t' '$1 == "FunInfoKey.lean" && $6 >= 2' fun_info.stats | grep -q . ||
  fail "FunInfoKey.lean reused too little: $(cat fun_info.stats)"
$DIFF -- fun_info_exact.out fun_info.out || fail "a key of the funInfo cache has the recording's names"
LEAN_PATH=. PAPERLEAN_REUSE_ORACLE=1 lean FunInfoKey.lean > fun_info_oracle.out 2>&1 ||
  fail "FunInfoKey.lean failed with the oracle: $(cat fun_info_oracle.out)"
LEAN_PATH=. oracle_fails stale-fun-info "an entry of the cache of .getFunInfo.)" FunInfoKey.lean
