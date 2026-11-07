import Lean
import Lean.Elab.Parallel

open Lean Meta Elab Tactic

private def alterCore : CoreM Unit := do
  modifyEnv (·.setMainModule `v023ParallelBranch)
  logInfo "discarded parallel message"

private def checkCore (env : Environment) (messages : MessageLog) : CoreM Unit := do
  unless (← getEnv).mainModule == env.mainModule do
    throwError "parallel branch environment escaped"
  unless (← Core.getMessageLog).toList.length == messages.toList.length do
    throwError "parallel branch message escaped"

run_meta do
  let env ← getEnv
  let messages ← Core.getMessageLog
  let rs ← Core.CoreM.par [do alterCore; pure 1, do alterCore; throwError "branch failed"]
  unless rs.length == 2 do throwError "lost task result"
  checkCore env messages
  let .ok (_, saved) := rs[0]! | throwError "first task failed"
  saved.restore
  unless (← getEnv).mainModule == `v023ParallelBranch do
    throwError "returned task state cannot be restored"
  setEnv env
  modifyThe Core.State fun s => { s with messages }
  let _ ← Core.CoreM.par' [alterCore, do alterCore; throwError "branch failed"]
  checkCore env messages

run_meta do
  let env ← getEnv
  let messages ← Core.getMessageLog
  let goal ← mkFreshExprMVar (mkConst ``True)
  let branch : MetaM Unit := do
    alterCore
    goal.mvarId!.assign (mkConst ``True.intro)
  let _ ← MetaM.par [branch, do branch; throwError "branch failed"]
  unless !(← goal.mvarId!.isAssigned) do throwError "MetaM.par kept assignment"
  checkCore env messages
  let _ ← MetaM.par' [branch]
  unless !(← goal.mvarId!.isAssigned) do throwError "MetaM.par' kept assignment"
  checkCore env messages

run_meta do
  Term.TermElabM.run' do
    let env ← getEnv
    let messages ← Core.getMessageLog
    let goal ← mkFreshExprMVar (mkConst ``True)
    let branch : TermElabM Unit := do
      alterCore
      goal.mvarId!.assign (mkConst ``True.intro)
      modify fun s => { s with pendingMVars := [goal.mvarId!] }
    let pending := (← get).pendingMVars
    let _ ← Term.TermElabM.par [branch, do branch; throwError "branch failed"]
    unless !(← goal.mvarId!.isAssigned) && (← get).pendingMVars == pending do
      throwError "TermElabM.par kept branch state"
    checkCore env messages
    let _ ← Term.TermElabM.par' [branch]
    unless !(← goal.mvarId!.isAssigned) && (← get).pendingMVars == pending do
      throwError "TermElabM.par' kept branch state"
    checkCore env messages

example : True := by
  run_tac do
    let env ← getEnv
    let messages ← Core.getMessageLog
    let goals ← getGoals
    let goal ← getMainGoal
    let branch : TacticM Unit := do
      alterCore
      goal.assign (mkConst ``True.intro)
      setGoals []
    let _ ← TacticM.par [branch, do branch; throwError "branch failed"]
    unless !(← goal.isAssigned) && (← getGoals) == goals do
      throwError "TacticM.par kept branch state"
    checkCore env messages
    let _ ← TacticM.par' [branch]
    unless !(← goal.isAssigned) && (← getGoals) == goals do
      throwError "TacticM.par' kept branch state"
    checkCore env messages
  trivial

-- Results and their saved states may contain generated names. The next parallel batch must
-- receive different child branches even when the previous batch's state was discarded.
run_meta do
  let collect : CoreM (Name × Name) := do return (← mkFreshId, ← mkAuxDeclName)
  let a ← Core.CoreM.par' [collect]
  let b ← Core.CoreM.par' [collect]
  let .ok a := a[0]! | throwError "name task failed"
  let .ok b := b[0]! | throwError "name task failed"
  unless a.1 != b.1 && a.2 != b.2 do throwError "parallel task names were reused"

-- A successful join installs the child's whole state. Its Core and Meta caches can mention
-- declarations from a different speculative branch with the very same name.
private def withBranchType (n ty : Name) : CoreM Unit :=
  addDecl (.axiomDecl { name := n, type := mkConst ty, levelParams := [], isUnsafe := false })

private def checkBranchCore (n : Name) (ty : Name) : CoreM Unit := do
  let ci ← getConstInfo n
  let actual ← Core.instantiateTypeLevelParams ci.toConstantVal []
  unless ci.type == mkConst ty && actual == ci.type do
    throwError "wrong Core type in parent or child: {n} : {actual}, expected {ty}"

private def checkBranchMeta (n : Name) (ty : Name) : MetaM Unit := do
  unless (← inferType (mkConst n)) == mkConst ty do
    throwError "wrong inferred type in parent or child: {n}, expected {ty}"
  checkBranchCore n ty

run_meta do
  let base ← getEnv
  let n := `v023ParentCore
  withBranchType n ``Nat
  let child : CoreM Unit := do setEnv base; withBranchType n ``Bool; checkBranchCore n ``Bool
  let [.ok _] ← Core.CoreM.par [child] | throwError "Core.par child failed"
  checkBranchCore n ``Nat
  let [.ok _] ← Core.CoreM.par' [child] | throwError "Core.par' child failed"
  checkBranchCore n ``Nat

run_meta do
  let base ← getEnv
  let n := `v023ParentMeta
  withBranchType n ``Nat
  let child : MetaM Unit := do setEnv base; withBranchType n ``Bool; checkBranchMeta n ``Bool
  let [.ok _] ← MetaM.par [child] | throwError "Meta.par child failed"
  checkBranchMeta n ``Nat
  let [.ok _] ← MetaM.par' [child] | throwError "Meta.par' child failed"
  checkBranchMeta n ``Nat

run_meta do
  Term.TermElabM.run' do
    let base ← getEnv
    let n := `v023ParentTerm
    withBranchType n ``Nat
    let child : TermElabM Unit := do setEnv base; withBranchType n ``Bool; checkBranchMeta n ``Bool
    let [.ok _] ← Term.TermElabM.par [child] | throwError "Term.par child failed"
    checkBranchMeta n ``Nat
    let [.ok _] ← Term.TermElabM.par' [child] | throwError "Term.par' child failed"
    checkBranchMeta n ``Nat

example : True := by
  run_tac do
    let base ← getEnv
    let n := `v023ParentTactic
    withBranchType n ``Nat
    let child : TacticM Unit := do setEnv base; withBranchType n ``Bool; checkBranchMeta n ``Bool
    let [.ok _] ← TacticM.par [child] | throwError "Tactic.par child failed"
    checkBranchMeta n ``Nat
    let [.ok _] ← TacticM.par' [child] | throwError "Tactic.par' child failed"
    checkBranchMeta n ``Nat
  trivial

-- Macro scopes are shared counters, unlike the split fresh-name generators. Every successful
-- child's high-water mark must survive, even when the last child allocated fewer scopes.
private def macroNames (n : Nat) : CoreM (List Name) := do
  (List.range n).mapM fun _ => mkFreshUserName `v023MacroName

private def checkParentMacro (names : List (List Name)) : CoreM Unit := do
  let parent ← mkFreshUserName `v023MacroName
  if names.flatten.contains parent then throwError "parallel child macro name reused in parent"

run_meta do
  let [.ok a, .ok b] ← Core.CoreM.par' [macroNames 4, macroNames 1] | throwError "child failed"
  checkParentMacro [a,b]
  let [.ok (a,_), .ok (b,_)] ← Core.CoreM.par [macroNames 4, macroNames 1] | throwError "child failed"
  checkParentMacro [a,b]
  let [.ok a, .ok b] ← MetaM.par' [macroNames 4, macroNames 1] | throwError "child failed"
  checkParentMacro [a,b]
  let [.ok (a,_), .ok (b,_)] ← MetaM.par [macroNames 4, macroNames 1] | throwError "child failed"
  checkParentMacro [a,b]

run_meta do
  Term.TermElabM.run' do
    let [.ok a, .ok b] ← Term.TermElabM.par' [macroNames 4, macroNames 1] | throwError "child failed"
    checkParentMacro [a,b]
    let [.ok (a,_), .ok (b,_)] ← Term.TermElabM.par [macroNames 4, macroNames 1] | throwError "child failed"
    checkParentMacro [a,b]

example : True := by
  run_tac do
    let [.ok a, .ok b] ← TacticM.par' [macroNames 4, macroNames 1] | throwError "child failed"
    checkParentMacro [a,b]
    let [.ok (a,_), .ok (b,_)] ← TacticM.par [macroNames 4, macroNames 1] | throwError "child failed"
    checkParentMacro [a,b]
  trivial

run_meta do
  let scope := (← getThe Core.State).nextMacroScope
  let [] ← Core.CoreM.par' ([] : List (CoreM Unit)) | throwError "empty batch returned a result"
  unless (← getThe Core.State).nextMacroScope == scope do throwError "empty batch changed scopes"
  let [.ok names, .error _] ← Core.CoreM.par' [macroNames 4, throwError "failed child"]
    | throwError "wrong failed batch"
  checkParentMacro [names]

-- Task quotations have deterministic disjoint contexts. Returned names can be installed
-- together in one environment, including names returned by nested task families.
private def checkTaskNames (names : List Name) : CoreM Unit := do
  let parent ← mkFreshUserName `v023TaskConstant
  let parentView := extractMacroScopes parent
  let all := parent :: names
  unless all.eraseDups.length == all.length do throwError "task macro names collided"
  for name in names do
    let view := extractMacroScopes name
    unless view.name == `v023TaskConstant && view.review == name do
      throwError "task name broke hygiene representation"
    unless view.imported == parentView.imported do
      throwError "task name introduced imported macro scopes"
  for name in all do
    addDecl (.axiomDecl { name, type := mkConst ``Nat, levelParams := [], isUnsafe := false })

private def taskName : CoreM Name := mkFreshUserName `v023TaskConstant

run_meta do
  let child : CoreM (List Name) := do
    let outer ← taskName
    let [.ok innerA, .ok innerB] ← Core.CoreM.par' [taskName, taskName]
      | throwError "nested child failed"
    return [outer, innerA, innerB]
  let [.ok left, .ok right] ← Core.CoreM.par' [child, child] | throwError "sibling failed"
  checkTaskNames (left ++ right)
  let [.ok (a,_), .ok (b,_)] ← Core.CoreM.par [taskName, taskName] | throwError "sibling failed"
  checkTaskNames [a,b]
  let [.ok a, .ok b] ← MetaM.par' [taskName, taskName] | throwError "sibling failed"
  checkTaskNames [a,b]
  Term.TermElabM.run' do
    let [.ok a, .ok b] ← Term.TermElabM.par' [taskName, taskName] | throwError "sibling failed"
    checkTaskNames [a,b]

example : True := by
  run_tac do
    let [.ok a, .ok b] ← TacticM.par' [taskName, taskName] | throwError "sibling failed"
    checkTaskNames [a,b]
  trivial

run_meta do
  let action : CoreM (List (Except Exception Name)) := Core.CoreM.par' [taskName, taskName]
  let context ← readThe Core.Context
  let state ← getThe Core.State
  let a ← action.run' context state
  let b ← action.run' context state
  let [.ok a₁, .ok a₂] := a | throwError "task failed"
  let [.ok b₁, .ok b₂] := b | throwError "task failed"
  unless a₁ == b₁ && a₂ == b₂ && a₁ != a₂ do
    throwError "task name generation depends on scheduling"
