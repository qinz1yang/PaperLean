module
import Lean
public import Lean.Elab.Tactic.Basic
open Lean Grind

-- Should not produce spurious issues.
-- Accept only grind's normal terminal unsolved result. Elaboration failures,
-- internal exceptions, and resource failures remain visible to the message guard.
open Lean Elab Tactic in
elab "assert_grind_incomplete" : tactic => do
  let incomplete ← try
      evalTactic (← `(tactic| grind))
      pure false
    catch ex =>
      match ex with
      | .error _ msg =>
        if (← msg.toString).startsWith "`grind` failed\n" then pure true else throw ex
      | _ => throw ex
  if incomplete then
    throwError "grind reached the expected unsolved result"
  else
    throwError "grind unexpectedly solved the negative example"

/-- error: grind reached the expected unsolved result -/
#guard_msgs in
set_option trace.sym.issues true in
example [Field α] (a b : α) : a*b + b*c = 2 → b = a⁻¹ := by
  assert_grind_incomplete
