/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import ProofBase

open Lean Elab Command

initialize releasePredecessor : IO.Ref (Option (IO Unit)) ← IO.mkRef none

elab "#hold_predecessor" : command => do
  let env ← getEnv
  let name := `pendingPredecessor
  let pending ← env.addConstAsync name .thm
  let val : TheoremVal := {
    name
    levelParams := []
    type := mkConst ``True
    value := mkConst ``True.intro
  }
  pending.commitConst pending.asyncEnv (some (.thmInfo val)) (some (.thmInfo val))
  let .ok checked := pending.asyncEnv.addDeclCore 2000000 1024 (.thmDecl val) none
    | throwError "invalid predecessor"
  releasePredecessor.set (some (pending.commitCheckEnv checked))
  setEnv pending.mainEnv
  unless !(← IO.hasFinished pending.mainEnv.checked) do throwError "predecessor is already checked"
  IO.println "pending predecessor held"

private def proofKind (thm : TheoremVal) : CommandElabM String := do
  let body := thm.value.getLambdaBody
  if body.isAppOfArity ``Eq.mp 4 then return "certificate"
  if body.getAppFn.isConstOf ``ProofBase.witness then return "original witness"
  throwError "unexpected theorem body"

elab "#observe_then_release " id:ident : command => do
  let env ← getEnv
  let some release ← releasePredecessor.get | throwError "no pending predecessor"
  try
    if ← IO.hasFinished env.checked then throwError "predecessor was released early"
    let name ← resolveGlobalConstNoOverload id
    let some (.thmInfo thm) := env.find? name | throwError "theorem body was unavailable"
    let kind ← proofKind thm
    if ← IO.hasFinished env.checked then throwError "checked chain advanced while observing the body"
    IO.println s!"theorem body visible before release: {kind}"
  finally
    release
    releasePredecessor.set none

elab "#finish_predecessor " id:ident : command => do
  let env ← getEnv
  let name ← resolveGlobalConstNoOverload id
  let checked := env.checked.get
  unless (checked.find? `pendingPredecessor).isSome && (checked.find? name).isSome do
    throwError "committed declarations missing"
  IO.println "predecessor and dependent frontend declaration checked"

elab "#compare_ready " ref:ident id:ident : command => do
  let env ← getEnv
  let refName ← resolveGlobalConstNoOverload ref
  let name ← resolveGlobalConstNoOverload id
  let some (.thmInfo a) := env.find? refName | throwError "missing pending theorem"
  let some (.thmInfo b) := env.find? name | throwError "missing ready theorem"
  unless a.type == b.type do throwError "theorem types differ"
  let pending ← proofKind a
  let ready ← proofKind b
  unless pending == ready do throwError "certificate choice depended on predecessor timing"
  IO.println s!"eligible ready theorem uses {ready}"
