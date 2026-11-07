# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
cd "$TMP_DIR"
cat > lakefile.lean <<'END'
import Lake
import Lake.PaperLean.SetupIndex
open Lake Lean System
open Lake DSL
package overlap
@[default_target] lean_lib TestModule

private def probeIndex (ws : Workspace) (mod : Lake.Module) : FetchM (Option FilePath) := do
  -- A legacy manual recorder cannot seed a workspace run. This fabricated
  -- local import would prevent an index if it replaced the selected header.
  PaperLean.SetupIndex.note ws mod true #[(⟨`NoSuchModule, false, false, false⟩, true)] id
  discard <| (← mod.input.fetch).await
  return (← PaperLean.SetupIndex.indexFor ws.dir mod).map (·.1)

script overlapTest do
  let ws ← getWorkspace
  let some mod := ws.findModule? `TestModule | error "missing TestModule"
  let alias := Lake.DSL.mkModuleFacetDecl ModuleExportInfo `exportInfo fun m =>
    Lake.Module.exportInfoFacetConfig.run m
  let custom := ws.addModuleFacetConfig alias.config
  -- The outer custom build asks for an index while another run is still active.
  custom.runBuild do
    ws.runBuild do
      if (← probeIndex custom mod).isSome then error "stock build enabled custom index"
      return Job.pure ()
    return Job.pure ()
  -- An index already issued to the outer build remains readable across a nested run.
  let issued ← ws.runBuild do
    let some file ← probeIndex ws mod | error "missing initial index"
    custom.runBuild do
      unless ← file.pathExists do error "outer index lost during nested start"
      if (← probeIndex custom mod).isSome then error "custom build used an index"
      return Job.pure ()
    unless ← file.pathExists do error "nested finish removed the live outer index"
    unless (← probeIndex ws mod).isSome do error "nested run disabled the outer workspace"
    return Job.pure file
  if ← issued.pathExists then error "final finish leaked an index"
  ws.runBuild do
    let some next ← probeIndex ws mod | error "eligible build could not start again"
    if next == issued then error "reused a retiring generation"
    return Job.pure ()
  -- Real module jobs in another eligible run can publish a distinct generation in
  -- the same directory; the inner finish retires only its own artifacts.
  ws.runBuild do
    let some outer ← probeIndex ws mod | error "no outer generation"
    let inner ← ws.runBuild do
      discard <| (← mod.leanArts.fetch).await
      let mut other := none
      for d in ← (ws.dir / ".lake" / "paperlean-setup").readDir do
        for f in ← d.path.readDir do
          if f.path != outer && f.path.extension == some "paperlean" && f.fileName.startsWith "setup-" then
            other := some f.path
      let some file := other | error "no independent generation for inner module job"
      unless ← outer.pathExists do error "inner job invalidated outer generation"
      return Job.pure file
    if ← inner.pathExists then error "inner generation was not retired"
    unless ← outer.pathExists do error "inner finish retired outer generation"
    return Job.pure ()
  -- Each public runner can execute a custom provider while another build is live.
  ws.runBuild do
    let some file ← probeIndex ws mod | error "missing index before fetch"
    custom.runFetchM do
      if (← probeIndex custom mod).isSome then error "custom fetch borrowed an index"
    unless ← file.pathExists do error "fetch retired an outer index"
    return Job.pure ()
  ws.runBuild do
    let some file ← probeIndex ws mod | error "missing index before no-build check"
    let ok ← custom.checkNoBuild do
      if (← probeIndex custom mod).isSome then error "custom no-build check borrowed an index"
      return Job.pure ()
    unless ok do error "no-build check failed"
    unless ← file.pathExists do error "no-build check retired an outer index"
    return Job.pure ()
  -- The last run can have a different directory than the run that published the file.
  let other := ws.dir / "second-workspace"
  PaperLean.SetupIndex.start ws.dir
  PaperLean.SetupIndex.note ws mod true (#[] : Array (Import × Bool)) id
  let some (file, _) ← PaperLean.SetupIndex.indexFor ws.dir mod | error "missing first workspace index"
  PaperLean.SetupIndex.start other
  PaperLean.SetupIndex.finish ws.dir
  unless ← file.pathExists do error "first finish removed a live generation"
  PaperLean.SetupIndex.finish other
  if ← file.pathExists then error "cleaned the wrong workspace"
  return 0
END
printf 'def testModule := 1\n' > TestModule.lean
run env PAPERLEAN_ACCELERATE=1 lake run overlapTest
