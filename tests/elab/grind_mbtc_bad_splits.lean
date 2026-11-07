import Lean

opaque p : α → Int → Int → Prop

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
example :
  a₁ ≥ 0 → a₂ ≥ 0 → a₃ ≥ 0 → a₄ ≥ 0 → a₅ ≥ 0 → a₆ ≥ 0 → a₇ ≥ 0 → a₈ ≥ 0 →
    p true a₁ a₂ → p 1 a₃ a₄ → p 'a' a₅ a₆ → p "" a₇ a₈ → False := by
  set_option trace.grind.split true in -- mbtc should not produce any case split
  assert_grind_incomplete
