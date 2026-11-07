# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
export LAKE_ARTIFACT_CACHE=false
root="$(cd "$TMP_DIR" && pwd -P)"
mkdir -p "$root/alt/CaseProbe" "$root/main/CaseProbe"
cd "$root/alt"
printf 'name="facetbug"\ndefaultTargets=["CaseProbe"]\n[[lean_lib]]\nname="CaseProbe"\n' > lakefile.toml
printf 'module\n@[expose] public def leaf := 17\n' > CaseProbe/Leaf.lean
printf 'module\npublic import CaseProbe.Leaf\n' > CaseProbe.lean
run lake build
export TEST_ALT_ARTIFACTS="$root/alt/.lake/build/lib/lean/CaseProbe"

cd "$root/main"
cat > lakefile.lean <<'END'
import Lake
open Lake Lean System
open Lake DSL
package facetbug
@[default_target] lean_lib CaseProbe

private def replaceParts (arts : ImportArtifacts) : IO ImportArtifacts := do
  let some dir ← IO.getEnv "TEST_ALT_ARTIFACTS" | throw (IO.userError "missing alternative artifacts")
  return ImportArtifacts.ofArrays <| arts.toArrays.map fun parts => parts.map fun p =>
    (dir : FilePath) / p.fileName.get!

private def exports : ModuleFacetDecl :=
  Lake.DSL.mkModuleFacetDecl ModuleExportInfo `exportInfo fun mod => do
    (← Lake.Module.exportInfoFacetConfig.run mod).mapM fun info => do
      if mod.name != `CaseProbe.Leaf then return info
      return {info with arts := ← replaceParts info.arts, allArts := ← replaceParts info.allArts}

private def presetups : ModuleFacetDecl :=
  Lake.DSL.mkModuleFacetDecl ModulePreSetup `presetup fun mod => do
    (← Lake.Module.presetupFacetConfig.run mod).mapM fun s => do
      if mod.name != `CaseProbe.Direct then return s
      let some arts := s.directImportArts.find? `CaseProbe.Leaf | error "missing leaf"
      return {s with directImportArts := s.directImportArts.insert `CaseProbe.Leaf (← replaceParts arts)}

private def inWorkspace (ws : Workspace) (work : FetchM α) : FetchM α := FetchM.ofFn fun fetch pkg? stack store ctx log =>
  work.toFn fetch pkg? stack store {ctx with opaqueWs := ws} log

-- Simulate a provider that intercepts an edge without changing the workspace.
private def withAnswer (key : BuildKey) (answer : Job (BuildData key)) (work : FetchM α) : FetchM α :=
  FetchM.ofFn fun fetch pkg? stack store ctx log =>
    let modified : IndexBuildFn RecBuildM := fun info =>
      if h : info.key = key then pure <| cast (congrArg (fun k => Job (BuildData k)) h.symm) answer
      else fetch info
    work.toFn modified pkg? stack store ctx log

-- Use a different store or replace a job in the existing store after a transitive
-- importer was cached. Ordinary Lake observes this replacement while walking that importer.
private def withStored (fresh : Bool) (key : BuildKey) (answer : Job (BuildData key))
    (work : FetchM α) : FetchM α :=
  FetchM.ofFn fun fetch pkg? stack store ctx log => do
    let ref ← if fresh then IO.mkRef (← store.get) else pure store
    ref.modify (·.insert key answer)
    work.toFn fetch pkg? stack ref ctx log

script switched (args) do
  let [mode] := args | error "expected a mode"
  let ws ← getWorkspace
  let targetName := if mode == "direct" || mode == "primePreset" then `CaseProbe.Direct else `CaseProbe.Transitive
  let some mod := ws.findModule? targetName | error "missing target"
  let some leaf := ws.findModule? `CaseProbe.Leaf | error "missing leaf"
  let custom := ws.addModuleFacetConfig (if mode == "primePreset" then presetups else exports).config
  discard <| ws.runBuild do
    if ["fetch", "nestedFetch", "failedNested", "store", "copiedStore"].contains mode then
      let some mid := ws.findModule? `CaseProbe.Middle | error "missing middle"
      discard <| (← mid.exportInfo.fetch).await
      let original ← leaf.exportInfo.fetch
      let alternate ← original.mapM fun info => do
        return {info with arts := ← replaceParts info.arts, allArts := ← replaceParts info.allArts}
      let answer : Job (BuildData leaf.exportInfo.key) := cast (by simp) alternate
      if mode == "nestedFetch" || mode == "failedNested" then
        -- An already-certified transitive closure may subsequently be reached through
        -- a different recursive dispatcher. The inner handler returns the actual stored
        -- middle job; the outer handler replaces only the hidden transitive leaf export.
        let middle : Job (BuildData mid.exportInfo.key) := cast (by simp) (← mid.exportInfo.fetch)
        let effective := if mode == "failedNested" then Job.error else answer
        withAnswer leaf.exportInfo.key effective <|
          withAnswer mid.exportInfo.key middle <| Lake.Module.leanArtsFacetConfig.run mod
      else if mode == "fetch" then
        withAnswer leaf.exportInfo.key answer <| Lake.Module.leanArtsFacetConfig.run mod
      else
        withStored (mode == "copiedStore") leaf.exportInfo.key answer mod.leanArts.fetch
    else if mode == "primeExport" then
      discard <| (← leaf.leanArts.fetch).await
      discard <| (← inWorkspace custom leaf.exportInfo.fetch).await
      mod.leanArts.fetch
    else if mode == "primePreset" then
      discard <| (← mod.input.fetch).await
      discard <| (← mod.importInfo.fetch).await
      discard <| (← inWorkspace custom mod.presetup.fetch).await
      mod.leanArts.fetch
    else
      inWorkspace custom mod.leanArts.fetch
  return 0

script payload (args) do
  let [mode] := args | error "expected a mode"
  let ws ← getWorkspace
  let some leaf := ws.findModule? `CaseProbe.Leaf | error "missing leaf"
  let some mod := ws.findModule? (if mode == "direct" then `CaseProbe.Direct else `CaseProbe.Transitive)
    | error "missing consumer"
  let pkg := { leaf.pkg with config := { leaf.pkg.config with buildDir := "alternate-build" } }
  let alternate := { leaf with lib := { leaf.lib with pkg } }
  discard <| ws.runBuild do
    discard <| (← leaf.input.fetch).await
    discard <| (← alternate.leanArts.fetch).await
    mod.leanArts.fetch
  return 0

script detached (args) do
  let [mode] := args | error "expected a mode"
  let ws ← getWorkspace
  let some mod := ws.findModule? (if mode == "direct" then `CaseProbe.Direct else `CaseProbe.Transitive)
    | error "missing consumer"
  let some changed := ws.findModule? (if mode == "direct" then `CaseProbe.Direct else `CaseProbe.Middle)
    | error "missing header"
  discard <| ws.runBuild do
    let source ← IO.FS.readFile changed.leanFile
    try
      IO.FS.writeFile changed.leanFile "module\n"
      discard <| (← Lake.Module.inputFacetConfig.run changed).await
    finally
      IO.FS.writeFile changed.leanFile source
    mod.leanArts.fetch
  let side := mod.irPath "setup.paperlean"
  let setup ← ModuleSetup.load (if ← side.pathExists then side else mod.setupFile)
  unless setup.importArts.contains `CaseProbe.Leaf do
    error "the real consumer setup omitted CaseProbe.Leaf"
  return 0
END
printf 'module\n@[expose] public def leaf := 7\n' > CaseProbe/Leaf.lean
printf 'module\npublic import CaseProbe.Leaf\nexample : leaf = 17 := rfl\n' > CaseProbe/Direct.lean
printf 'module\npublic import CaseProbe.Leaf\n' > CaseProbe/Middle.lean
printf 'module\npublic import CaseProbe.Middle\nexample : leaf = 17 := rfl\n' > CaseProbe/Transitive.lean
printf 'module\npublic import CaseProbe.Transitive\n' > CaseProbe.lean

# The alternately selected artifact must reach the frontend in the whole switched
# context and when only an upstream provider ran there before the caller restored it.
for mode in direct transitive primeExport primePreset fetch nestedFetch store copiedStore; do
  rm -rf .lake/build
  run env -u PAPERLEAN_ACCELERATE lake run switched "$mode"
  rm -rf .lake/build
  run env PAPERLEAN_ACCELERATE=1 lake run switched "$mode"
done

# Same build key, distinct package build directories. Only the alternate
# directory contains the selected Leaf, both directly and two imports down.
printf 'module\npublic import CaseProbe.Middle\nexample : leaf = 7 := rfl\n' > CaseProbe/Transitive.lean
for accelerated in 0 1; do
  rm -rf .lake/build
  if env PAPERLEAN_ACCELERATE="$accelerated" lake run switched failedNested; then
    fail "a failed replacement export was skipped by the transitive setup"
  fi
  [ ! -f .lake/build/lib/lean/CaseProbe/Transitive.olean ] || fail "compiled despite failed export"
done
printf 'module\npublic import CaseProbe.Leaf\nexample : leaf = 7 := rfl\n' > CaseProbe/Direct.lean
printf 'module\npublic import CaseProbe.Middle\nexample : leaf = 7 := rfl\n' > CaseProbe/Transitive.lean
for mode in direct transitive; do
  for script in payload detached; do
    rm -rf .lake/build alternate-build
    run env -u PAPERLEAN_ACCELERATE lake run "$script" "$mode"
    rm -rf .lake/build alternate-build
    run env PAPERLEAN_SETUP_INDEX_KEEP=1 PAPERLEAN_ACCELERATE=1 lake run "$script" "$mode"
  done
done
