module
public import Finish
import Lean
example {n} (a b : V (n+1)) : @V.project _ a b Ix.zero = Prod.fst := by
  rw [V.project.eq_2]

open Lean Meta in
run_meta do
  let info ← getConstInfo ``V.captured.eq_2
  let some (_, _, rhs) := info.type.getForallBody.eq? | throwError "expected an equation"
  unless (isMatcherAppCore? (← getEnv) rhs).isSome do
    throwError "the constructor branch capturing x changed its published form"
