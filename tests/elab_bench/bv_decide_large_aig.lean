import Std.Tactic.BVDecide
import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.BVDecide.Main
import Lean.Meta.Tactic.BVDecide.TacticContext
import Lean.Meta.Tactic.Grind.Main

-- This test exercises the AIG infrastructure, producing a giant AIG that needs to be serialized etc
private def largeAIGProblem : Prop := ∀ (v6 v5 v1 v3 v2 v4 : BitVec 128),
    (v2.smtUDiv v3).smtUDiv ((v1.smtUDiv v2).smtUDiv (v1.smtUDiv v3)) != v6 * v4.smtUDiv v5

open Lean Meta in
run_meta do
  let .defnInfo problem ← getConstInfo ``largeAIGProblem | throwError "expected a definition"
  forallTelescope problem.value fun _ target => do
    let goal := (← mkFreshExprMVar target).mvarId!
    Lean.Elab.Term.TermElabM.run' do
      IO.FS.withTempFile fun _ lratFile => do
        let ctx ← Lean.Meta.Tactic.BVDecide.TacticContext.new lratFile {}
        let params ← Lean.Meta.Grind.mkDefaultParams {}
        let result ← Lean.Meta.Grind.GrindM.run (params := params) <|
          Lean.Meta.Tactic.BVDecide.bvDecide' (.mvarIdTarget goal) ctx
        match result with
        | .ok _ => throwError "expected a counterexample for the large AIG"
        | .error counterExample =>
          -- This typed result is produced after AIG construction, CNF serialization,
          -- and the external solver. Exceptions from earlier stages must escape.
          if counterExample.equations.isEmpty then
            throwError "large AIG produced an empty counterexample"
