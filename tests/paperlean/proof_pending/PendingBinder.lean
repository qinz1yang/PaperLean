import Lean
import ProofBase
import Lean.PaperLean.ProofConversion

open Lean Meta ProofBase
universe u

set_option paperlean.proofConversion false in
theorem original {α : Type u} (x : α) (n : Nat) : Holds (target x n) := witness x n

run_meta do
  let env ← getEnv
  let some (.thmInfo t) := env.find? ``original | throwError "missing original"
  let held := `HeldBinderType
  let pending ← env.addConstAsync held .defn (reportExts := false)
  let alias : DefinitionVal := {
    name := held, levelParams := [], type := mkSort 1, value := mkConst ``Nat,
    hints := .abbrev, safety := .safe, all := [held] }
  pending.commitSignature alias.toConstantVal
  let name := `heldBinderTheorem
  let d := { t with
    name, all := [name],
    type := mkForall `unused .default (mkConst held) t.type,
    value := mkLambda `unused .default (mkConst held) t.value }
  -- No task can complete HeldBinderType until optimize finishes. The surrounding
  -- test runner bounds the process if it accidentally demands that constant.
  setEnv pending.mainEnv
  try
    let result ← PaperLean.ProofConversion.optimize d
    unless Expr.equal result.value d.value do throwError "unexpected rewrite"
  finally
    setEnv env
    pending.commitConst pending.asyncEnv (some (.defnInfo alias)) (some (.defnInfo alias))
    let .ok checked := pending.asyncEnv.addDeclCore 2000000 1024 (.defnDecl alias) none
      | throwError "invalid predecessor"
    pending.commitCheckEnv checked
