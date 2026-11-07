# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
cd "$TMP_DIR"
export LAKE_ARTIFACT_CACHE=false
cat > lakefile.lean <<'END'
import Lake
import Lake.PaperLean.SetupIndex
open Lake
open Lake DSL
package witness
@[default_target] lean_lib Witness

private def withNoBuild (active : Bool) (x : FetchM α) : FetchM α :=
  FetchM.ofFn fun f p stack store ctx log =>
    x.toFn f p stack store {ctx with noBuild := active} log

private def withAnswer (key : BuildKey) (answer : Job (BuildData key)) (x : FetchM α) : FetchM α :=
  FetchM.ofFn fun fetch pkg? stack store ctx log =>
    let modified : IndexBuildFn RecBuildM := fun info =>
      if h : info.key = key then pure <| cast (congrArg (fun k => Job (BuildData k)) h.symm) answer
      else fetch info
    x.toFn modified pkg? stack store ctx log

private def inWorkspace (ws : Workspace) (x : FetchM α) : FetchM α :=
  FetchM.ofFn fun f p stack store ctx log => x.toFn f p stack store {ctx with opaqueWs := ws} log

private def checkOwner (expected : Bool) : FetchM Unit := do
  unless (← PaperLean.SetupIndex.observesProviders (← getBuildContext)) == expected do
    error s!"wrong setup provider admission; expected {expected}"

script verify do
  let ws ← getWorkspace
  let some mod := ws.findModule? `Witness | error "missing module"
  let accelerated := (← IO.getEnv "PAPERLEAN_ACCELERATE") == some "1"
  discard <| ws.runBuild (cfg := {noBuild := true}) do
    checkOwner false
    withNoBuild false <| checkOwner false
    discard <| (← mod.input.fetch).await
    if (← PaperLean.SetupIndex.indexFor ws.dir mod).isSome then error "no-build owner issued an index"
    return Job.pure ()
  discard <| ws.runBuild do
    checkOwner accelerated
    withNoBuild true <| checkOwner accelerated
    ws.runBuild (cfg := {noBuild := true}) do
      checkOwner false
      return Job.pure ()
    checkOwner accelerated
    discard <| (← mod.input.fetch).await
    unless (← PaperLean.SetupIndex.indexFor ws.dir mod).isSome == accelerated do
      error "ordinary owner index availability changed"
    return Job.pure ()
  if accelerated then
    -- A local no-build flag in a regular owner cannot conceal a substituted job.
    ws.runBuild do
      let original ← mod.input.fetch
      let fake := original.map fun input => {input with header := {input.header with isModule := false}}
      let fake : Job (BuildData mod.input.key) := cast (by simp) fake
      withNoBuild true <| withAnswer mod.input.key fake <| do discard (← mod.input.fetch).await
      checkOwner false
      return Job.pure ()
    -- The same applies to an actual cached lookup in a different workspace, even
    -- after returning to the original workspace.
    let alias := Lake.DSL.mkModuleFacetDecl ModuleExportInfo `exportInfo fun m =>
      Lake.Module.exportInfoFacetConfig.run m
    let custom := ws.addModuleFacetConfig alias.config
    ws.runBuild do
      discard (← mod.input.fetch).await
      withNoBuild true <| inWorkspace custom <| do discard (← mod.input.fetch).await
      checkOwner false
      return Job.pure ()
  return 0
END
printf 'module\npublic def witness := 1\n' > Witness.lean
run env -u PAPERLEAN_ACCELERATE lake run verify
run env PAPERLEAN_ACCELERATE=1 lake run verify
if env PAPERLEAN_ACCELERATE=1 lake build --no-build +Witness; then
  fail "stale no-build unexpectedly succeeded"
else
  [ "$?" -eq 3 ] || fail "stale no-build had the wrong exit status"
fi
[ ! -f .lake/build/lib/lean/Witness.olean ] || fail "no-build compiled a stale target"
run env PAPERLEAN_ACCELERATE=1 lake build +Witness
run env PAPERLEAN_ACCELERATE=1 lake build --no-build +Witness
