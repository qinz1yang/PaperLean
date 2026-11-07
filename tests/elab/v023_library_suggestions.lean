module
import Lean
import all Lean.LibrarySuggestions.Basic
import all Lean.LibrarySuggestions.SymbolFrequency
import all Lean.LibrarySuggestions.SineQuaNon

open Lean Meta LibrarySuggestions LibrarySuggestions.SineQuaNon

theorem v023SuggestionOne : True := trivial
theorem v023SuggestionTwo : True := trivial

run_meta do
  let g := (← mkFreshExprMVar (mkConst ``True)).mvarId!
  let localSuggestions ← currentFile g { maxSuggestions := 1, filter := fun n => pure (n == ``v023SuggestionTwo) }
  unless localSuggestions.map (·.name) == #[``v023SuggestionTwo] do
    throwError "currentFile ignored Config.filter"
  let rejected ← (random (gen := ⟨37, 59⟩)) g { maxSuggestions := 2, filter := fun _ => pure false }
  unless rejected.isEmpty do throwError "random ignored the rejecting filter"
  let one ← (random (gen := ⟨37, 59⟩)) g { maxSuggestions := 4, filter := fun n => pure (n == ``Nat.add_comm) }
  unless one.size == 4 && one.all (·.name == ``Nat.add_comm) do
    throwError "random did not sample its filtered candidates"
  let saved ← sineQuaNonTriggersRef.get
  try
    let triggers := ({} : NameMap (List (Name × Float))).insert ``True
      [(``v023SuggestionOne, 1.0), (``v023SuggestionOne, 2.0), (``v023SuggestionTwo, 3.0)]
    let triggers := triggers.insert ``Eq [(``v023SuggestionOne, 1.0)]
    let cell ← sineQuaNonTriggersRef.cell (← IndexContext.current) IndexContext.same
    cell.set (some (.pure (some triggers)))
    unless (← sineQuaNon (NameSet.ofList [``Eq]) 1).isEmpty do
      throwError "Sine Qua Non used a denied trigger"
    let xs ← sineQuaNon (NameSet.ofList [``True]) 2
    unless xs.map (·.name) == #[``v023SuggestionOne, ``v023SuggestionTwo] do
      throwError "the same theorem consumed more than one suggestion slot"
    let unweighted ← sineQuaNon (NameSet.ofList [``True]) 1 1.5 0.0
    let some first := unweighted[0]? | throwError "unweighted search returned no suggestion"
    unless first.score == 1.0 do
      throwError "initial triggers ignored frequencyWeight"
    let ys ← (sineQuaNonSelector (depthFactor := 1.5)) g {
      maxSuggestions := 1
      filter := fun n => pure (n == ``v023SuggestionTwo)
    }
    unless ys.map (·.name) == #[``v023SuggestionTwo] do
      throwError "Sine Qua Non ignored the filter or charged rejected candidates to the budget"
    let zs ← (sineQuaNonSelector (depthFactor := 1.5)) g { maxSuggestions := 0 }
    unless zs.isEmpty do throwError "zero budget returned suggestions"
  finally
    sineQuaNonTriggersRef.set saved

-- Warming frequencies, changing a local premise policy, then asking for triggers used to
-- return forbidden declarations. Restoring the earlier environment must restore its results.
run_meta do
  let initial ← getEnv
  let marker := ``HAppend.hAppend
  let premise := ``List.append_assoc
  let includesPremise : CoreM Bool := do
    return (← sineQuaNonTheorems marker).any fun (n, _) => n == premise
  let before ← symbolFrequency marker
  unless before > 0 do throwError "missing imported marker"
  modifyEnv fun env => nameDenyListExt.addEntry env "List"
  unless isDeniedPremise (← getEnv) premise do throwError "failed to deny premise"
  if ← includesPremise then throwError "warm frequency admitted a denied premise"
  unless (← symbolFrequency marker) < before do throwError "frequency ignored the changed policy"
  setEnv initial
  unless ← includesPremise do throwError "rollback kept the denied result"
  modifyEnv fun env => triggerDenyListExt.addEntry env marker
  unless (← sineQuaNonTheorems marker).isEmpty do throwError "warm index ignored a denied trigger"
  setEnv initial
  unless ← includesPremise do throwError "rollback kept the denied trigger"

-- An older in-flight computation must finish in its own cell, even if a new revision has
-- replaced the process's cache entry. Different options receive separate cells as well.
run_meta do
  let cache : IndexCache Nat ← IO.mkRef none
  let tk ← IO.CancelToken.new
  let started ← IO.Promise.new
  let release ← IO.Promise.new
  let old ← Core.wrapAsync (fun (_ : Unit) => cache.getOrCompute do
    started.resolve ()
    IO.wait release.result!
    return 1) (some tk)
  let first ← EIO.asTask (old ())
  IO.wait started.result!
  let initial ← getEnv
  modifyEnv fun env => nameDenyListExt.addEntry env "List"
  try
    unless (← cache.getOrCompute (pure 2)) == 2 do throwError "waited on stale index"
  finally
    release.resolve ()
  let .ok 1 ← IO.wait first | throwError "old computation lost its result"
  unless (← cache.getOrCompute (pure 3)) == 2 do throwError "old computation overwrote newer index"
  withOptions (fun opts => opts.setBool `v023.suggestion.test true) do
    unless (← cache.getOrCompute (pure 4)) == 4 do throwError "options reused stale index"
  setEnv initial
  unless (← cache.getOrCompute (pure 1)) == 1 do throwError "rollback reused the wrong index"

private unsafe def importInitForSuggestions : IO Environment := do
  enableInitializersExecution
  importModules (loadExts := true) #[{ module := `Init }] {}

-- Two frontends can use different import environments in one process. The persistent
-- imported table from Std must never satisfy a query in an Init-only environment.
run_meta do
  let original ← getEnv
  let small ← importInitForSuggestions
  let symbol := `Std.HashMap.isEmpty
  unless original.contains symbol && !small.contains symbol do throwError "missing import control"
  let fullFrequency ← symbolFrequency symbol
  unless fullFrequency > 0 do throwError "expected imported Std theorems"
  try
    setEnv small
    unless (← symbolFrequency symbol) == 0 do throwError "reused the larger imports"
  finally
    setEnv original
  unless (← symbolFrequency symbol) == fullFrequency do throwError "lost the restored imports"
