# Tests the reuse of typeclass results across commands (`Lean.PaperLean.TCCache`): the output is Lean
# 4.35.0-rc3's (the expected output below is official Lean's) for theorems of a section that solve
# the same problems, a theorem with another local instance of the class (another problem, whose
# result is another instance), and problems whose result an instance added later changes (with a
# lower priority, which does not change the result, and a higher one, which does); results are
# reused; and every reuse agrees with Lean's search (`PAPERLEAN_REUSE_ORACLE`).

cat > "$TMP_DIR/TCCache.lean" <<'EOF'
class Foo (α : Type) where
  foo : α
class Bar (α : Type) extends Foo α where
  bar : α
instance : Foo Nat := ⟨0⟩

section
variable {α : Type} [Bar α] [Add α]
theorem t1 (x : α) : x + Foo.foo = x + Foo.foo := rfl
theorem t2 (y : α) : y + Foo.foo = y + Foo.foo := rfl
theorem t3 (z : α) : Foo.foo + z = Foo.foo + z := rfl
-- another local instance of the class: another problem
theorem t4 [inst : Foo α] : (Foo.foo : α) = @Foo.foo α inst := rfl
theorem t5 : (Foo.foo : α) = @Foo.foo α Bar.toFoo := rfl
#check @t3
#check @t4
end

example : (Foo.foo : Nat) = 0 := rfl
example : (Foo.foo : Nat) = 0 := rfl
instance (priority := low) fooNat1 : Foo Nat := ⟨1⟩
example : (Foo.foo : Nat) = 0 := rfl
-- an instance that Lean prefers: the earlier result no longer holds
instance (priority := high) fooNat2 : Foo Nat := ⟨2⟩
example : (Foo.foo : Nat) = 2 := rfl
example : (Foo.foo : Nat) = 2 := rfl
#check (Foo.foo : Nat)
EOF
cat > "$TMP_DIR/expected.out" <<'EOF'
TCCache.lean:13:0: warning: automatically included section variable(s) unused in theorem `t4`:
  [Bar α]
  [Add α]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [Bar α] [Add α] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
TCCache.lean:14:0: warning: automatically included section variable(s) unused in theorem `t5`:
  [Add α]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [Add α] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
@t3 : ∀ {α : Type} [inst : Bar α] [inst_1 : Add α] (z : α), Foo.foo + z = Foo.foo + z
@t4 : ∀ {α : Type} [Bar α] [Add α] [inst : Foo α], Foo.foo = Foo.foo
Foo.foo : Nat
EOF
cd "$TMP_DIR"
capture_exit 0 lean TCCache.lean
$DIFF -- expected.out "$CAPTURED.out.produced" || fail "the output differs from Lean's"
# every reuse agrees with Lean's search, so nothing runs again
PAPERLEAN_REUSE_ORACLE=1 PAPERLEAN_REUSE_LOG=rerun.log lean TCCache.lean > oracle.out 2>&1 || fail "lean failed"
if [ -s rerun.log ]; then fail "a reuse differs from Lean's search: $(cat rerun.log)"; fi
$DIFF -- expected.out oracle.out || fail "the output with the oracle differs from Lean's"
# results were reused
{ echo "import Lean"; cat TCCache.lean; echo 'run_cmd do let (r, n, f) ← Lean.PaperLean.TCCache.stats; Lean.logInfo m!"reused {r}, searched {n}, of them after a change {f}"'; } > Stats.lean
lean Stats.lean > stats.out 2>&1
R=$(sed -n 's/.*reused \([0-9]*\), searched \([0-9]*\), of them after a change \([0-9]*\).*/\1 \3/p' stats.out)
set -- $R
[ -n "${1:-}" ] && [ "$1" -ge 3 ] || fail "too few reuses: $(tail -2 stats.out)"
[ "${2:-0}" -ge 1 ] || fail "the change of instances was not noticed: $(tail -2 stats.out)"
