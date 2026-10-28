# Tests the reuse of section variables (`Lean.PaperLean.SectionVars`): the output is Lean
# 4.35.0-rc3's (the expected output below is official Lean's) for declarations that use the variables
# of earlier ones, also with `include` and `variable ... in`; for a namespace in which the type of a
# variable means another constant, and for an `open` after which it is ambiguous (Lean then
# elaborates it as `sorry`), where the recorded name resolution no longer holds and the variables are
# elaborated again; for instances, whose header is elaborated twice, and the declarations after
# them; for binders whose elaboration records a module use (`Lean.ExtraModUses`), where the
# module uses are Lean's; and for binders of a user elaborator, which are not reused with
# `PAPERLEAN_REUSE_USER_ELABS=0`. Every reuse is also compared with Lean's elaboration
# (`PAPERLEAN_REUSE_ORACLE`).

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
@i1 : ∀ {α β : Type u_1} [inst : C α] [inst_1 : C β], D.d = (C.x, C.x)
@i2 : ∀ {α : Type u_1} [inst : C α], D.d = C.x
EOF
cd "$TMP_DIR"
capture_exit 0 lean SectionVars.lean
$DIFF -- expected.out "$CAPTURED.out.produced" || fail "the output differs from Lean's"
# every reuse agrees with Lean's elaboration, so nothing runs again
PAPERLEAN_REUSE_ORACLE=1 PAPERLEAN_REUSE_LOG=reuse.log lean SectionVars.lean \
  > run.out 2>&1 || fail "lean failed"
if [ -s reuse.log ]; then fail "a reuse differs from Lean's elaboration: $(cat reuse.log)"; fi
$DIFF -- expected.out run.out || fail "the output with the oracle differs from Lean's"
# the variables were reused, and elaborated again where the name resolution changed
{ echo "import Lean"; cat SectionVars.lean; echo 'run_cmd do let (r, n, f) ← Lean.PaperLean.SectionVars.stats; Lean.logInfo m!"reused {r}, elaborated {n}, of them after a change {f}"'; } > Stats.lean
lean Stats.lean > stats.out 2>&1
R=$(sed -n 's/.*reused \([0-9]*\), elaborated \([0-9]*\), of them after a change \([0-9]*\).*/\1 \3/p' stats.out)
set -- $R
[ -n "${1:-}" ] && [ "$1" -ge 6 ] || fail "too few reuses: $(tail -2 stats.out)"
[ "${2:-0}" -ge 2 ] || fail "the changed name resolutions were not noticed: $(tail -2 stats.out)"
# binders whose elaboration records a module use (the macro of the notation `×`, from
# `Init.Notation`) are reused too, and the module uses recorded are Lean's (the expected output is
# official Lean's)
cat > Uses.lean <<'EOF2'
variable (p : Nat × Nat) (q : List (Nat × Nat))
theorem u1 : p = p := rfl
theorem u2 : q = q ∧ p = p := ⟨rfl, rfl⟩
theorem u3 : p.1 = p.1 := rfl
EOF2
cat > ReadUses.lean <<'EOF2'
import Lean
import Uses
open Lean in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Uses | throwError "no module Uses"
  let uses := (getExtraModUses env idx).map fun u => s!"{u.module} {u.isExported} {u.isMeta}"
  logInfo m!"{uses.qsort (· < ·) |>.toList}"
EOF2
mkdir -p lib
lean -o lib/Uses.olean Uses.lean > uses.out 2>&1 || fail "Uses.lean failed: $(cat uses.out)"
LEAN_PATH=lib lean ReadUses.lean > read_uses.out 2>&1 || fail "ReadUses.lean failed: $(cat read_uses.out)"
echo "[Init.Notation false false]" | $DIFF -- - read_uses.out || fail "the module uses differ from Lean's"
{ echo "import Lean"; cat Uses.lean; echo 'run_cmd do let (r, _, _) ← Lean.PaperLean.SectionVars.stats; Lean.logInfo m!"reused {r}"'; } > UsesStats.lean
lean UsesStats.lean > uses_stats.out 2>&1
R=$(sed -n 's/.*reused \([0-9]*\).*/\1/p' uses_stats.out)
[ -n "$R" ] && [ "$R" -ge 2 ] || fail "binders that record a module use were not reused: $(tail -2 uses_stats.out)"
# binders that a user elaborator elaborates are reused by default, and not with
# `PAPERLEAN_REUSE_USER_ELABS=0`
cat > UserElab.lean <<'EOF2'
import Lean
open Lean Elab Term in
elab "natType%" : term => return mkConst ``Nat
variable (n : natType%)
theorem e1 : n = n := rfl
theorem e2 : n = n := rfl
theorem e3 : n + 0 = n := rfl
run_cmd do let (r, _, _) ← Lean.PaperLean.SectionVars.stats; Lean.logInfo m!"reused {r}"
EOF2
lean UserElab.lean > user_elab.out 2>&1
R=$(sed -n 's/.*reused \([0-9]*\).*/\1/p' user_elab.out)
[ -n "$R" ] && [ "$R" -ge 2 ] || fail "binders of a user elaborator were not reused: $(tail -2 user_elab.out)"
PAPERLEAN_REUSE_USER_ELABS=0 lean UserElab.lean > user_elab0.out 2>&1
R=$(sed -n 's/.*reused \([0-9]*\).*/\1/p' user_elab0.out)
[ "$R" = 0 ] || fail "binders of a user elaborator were reused with PAPERLEAN_REUSE_USER_ELABS=0: $(tail -2 user_elab0.out)"
