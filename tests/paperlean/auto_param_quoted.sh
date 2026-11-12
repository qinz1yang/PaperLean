# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# `Lean.PaperLean.QuotedSyntax`: the tactic of an auto-param of this module is read off the
# definition that `declareTacticSyntax` made instead of being evaluated, so that a proof applying a
# lemma of the same file does not wait for the proofs before it. The elaboration must be exactly
# that of evaluating it (`PAPERLEAN_QUOTED_SYNTAX=0`), also where the constant must be evaluated:
# `implemented_by` (whose value would be a broken tactic here) and imported auto-params.

cd "$TMP_DIR"
cat > Imp.lean <<'EOF'
theorem importedAuto (n : Nat) (h : 0 < n + 1 := by omega) : n + 1 ≠ 0 := by omega
EOF
cat > Main.lean <<'EOF'
import Lean
open Lean

-- a slow proof before the lemmas: with evaluation, the proofs below wait for it
theorem slow : True := by sleep 1500; trivial

-- an auto-param of a lemma of this file, filled in later proofs and terms
theorem withAuto (n : Nat) (h : 0 < n + 1 := by omega) : n + 1 ≠ 0 := by omega
theorem uses (m : Nat) : m + 1 ≠ 0 := withAuto m
example : (3 : Nat) + 1 ≠ 0 := by exact withAuto 3

-- identifiers, atoms and nested nodes in the quoted tactic
def five := 5
theorem withSimp (h : five = 5 ∧ True := by simp only [five, and_true]) : five = 5 := h.1
example : five = 5 := withSimp

-- a structure field's auto-param (structure instance elaboration)
structure S where
  x : Nat
  h : x < 10 := by decide
def s : S := { x := 3 }
#eval s.x

-- the auto-param syntax as `#print` shows it
#print withAuto
#print withSimp
EOF
# constants that are evaluated as before: imported ones, and one with `implemented_by`, whose value
# (a broken tactic) is not what evaluating it gives (here Lean cannot evaluate it at all: the same
# error either way)
cat > Eval.lean <<'EOF'
import Lean
import Imp
open Lean

theorem usesImported (m : Nat) : m + 1 ≠ 0 := importedAuto m
#eval (3 : Nat)
EOF
cat > Impl.lean <<'EOF'
import Lean
open Lean

def goodTac : Syntax := Unhygienic.run `(tactic| trivial)
@[implemented_by goodTac] def tacByImpl : Syntax := mkAtom "this_is_not_a_tactic"
theorem withImpl (h : autoParam True tacByImpl) : True := h
example : True := withImpl
EOF
run lean -o Imp.olean Imp.lean
for f in Main Eval; do
  for v in "" 0; do
    capture env LEAN_PATH="$TMP_DIR" PAPERLEAN_QUOTED_SYNTAX="$v" lean $f.lean
    check_out_contains "3"
    cp "$CAPTURED.out.produced" "$TMP_DIR/$f.q${v:-on}"
  done
  $DIFF -- "$TMP_DIR/$f.qon" "$TMP_DIR/$f.q0" || fail "elaboration of $f differs from evaluating the tactic constants"
  if grep -q "error" "$TMP_DIR/$f.qon"; then fail "unexpected error in $f"; fi
done
for v in "" 0; do
  capture_fail env LEAN_PATH="$TMP_DIR" PAPERLEAN_QUOTED_SYNTAX="$v" lean Impl.lean
  cp "$CAPTURED.out.produced" "$TMP_DIR/Impl.q${v:-on}"
done
$DIFF -- "$TMP_DIR/Impl.qon" "$TMP_DIR/Impl.q0" || fail "a constant with implemented_by was not evaluated"
# the wait itself (`-Dprofiler=true` on the command line reports each blocked `Task.get` with a
# backtrace): evaluating `withAuto`'s tactic waits for `slow`; reading it does not
# (`evalSyntaxConstant`, or `evalConstCheck` that it tail-calls, is on the stack of any wait while
# getting the tactic, whichever way)
capture env LEAN_PATH="$TMP_DIR" PAPERLEAN_QUOTED_SYNTAX=0 LEAN_TRACE_TASK_GET_BLOCKED=1 lean -Dprofiler=true Main.lean
grep -qE "evalSyntaxConstant|evalConstCheck" "$CAPTURED.out.produced" || fail "evaluating the tactic did not wait"
capture env LEAN_PATH="$TMP_DIR" LEAN_TRACE_TASK_GET_BLOCKED=1 lean -Dprofiler=true Main.lean
if grep -qE "evalSyntaxConstant|evalConstCheck" "$CAPTURED.out.produced"; then
  fail "getting the auto-param's tactic waited for other branches"
fi
true
