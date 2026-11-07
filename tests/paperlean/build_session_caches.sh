# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
cd "$TMP_DIR"
unset PAPERLEAN_DATA PAPERLEAN_BUILD_PACKS_KEEP PAPERLEAN_FREE_SPACE LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
export PAPERLEAN_ACCELERATE=1 PAPERLEAN_HASH_CACHE=1 PAPERLEAN_BUILD_PACKS=1 PAPERLEAN_BUILD_PACK_BATCH=1
export PAPERLEAN_CACHE_DIR="$PWD/cache"
mkdir -p .lake/build/lib/lean empty-lib
printf 'def probe := 42\n' > Probe.lean
run lean -o .lake/build/lib/lean/Probe.olean Probe.lean
printf 0123456789abcdef > outer.hash
printf fedcba9876543210 > inner.hash
# Hash records only admit files older than the implementation's coarse-clock margin.
sleep 3
cat > lakefile.lean <<'LEAN'
import Lake
import Lake.PaperLean.BuildData
import Lake.PaperLean.BuildEnv
import Lake.PaperLean.HashCache
open Lake System
open Lake DSL
package SessionOwnership
lean_lib Probe

private def paths (env : Array (String × Option String)) : List String :=
  match (env.find? (·.1 == "LEAN_OLEAN_PACK")).bind Prod.snd with
  | some v => v.splitOn ":"
  | none => []

private def awaitPack (ctx : BuildContext) : IO FilePath := do
  for _ in [0:500] do
    if let some path := (paths (← PaperLean.BuildData.leanEnvFor ctx)).find? (·.endsWith "pack-0.paperlean") then
      return path
    IO.sleep 10
  throw (IO.userError "pack was never published to its owner")

private def readHash (ctx : BuildContext) (file : FilePath) : IO Unit := do
  let some expected ← Hash.load? file | throw (IO.userError "invalid test hash")
  unless (← PaperLean.HashCache.loadFor? ctx file) == some expected do
    throw (IO.userError "hash lookup disagrees with Lean")

private def makePack (ctx : BuildContext) (ws : Workspace) (mod : Lake.Module) : IO FilePath := do
  PaperLean.BuildData.compileStartingFor ctx mod ws.dir (ws.dir / "empty-lib")
  PaperLean.BuildData.moduleDoneFor ctx mod
  awaitPack ctx

private def checkInner (ws : Workspace) (mod : Lake.Module) (outer : BuildContext)
    (a : FilePath) (marker : String) : FetchM (Job FilePath) := do
  let inner ← getBuildContext
  let before := paths (← PaperLean.BuildData.leanEnvFor inner)
  unless before.isEmpty do error "inner inherited outer packs"
  unless (paths (← PaperLean.BuildEnv.leanEnv)).isEmpty do error "legacy lookup borrowed a run"
  PaperLean.BuildEnv.addPack "unowned"
  readHash inner (ws.dir / "inner.hash")
  let b ← makePack inner ws mod
  if a == b || !(← a.pathExists) || !(← b.pathExists) then error "packs did not coexist"
  let bEnv := paths (← PaperLean.BuildData.leanEnvFor inner)
  let aEnv := paths (← PaperLean.BuildData.leanEnvFor outer)
  if bEnv.contains marker || bEnv.contains a.toString || bEnv.contains "unowned" ||
      aEnv.contains b.toString || aEnv.contains "unowned" || !aEnv.contains marker then
    error "environment crosses ownership"
  return Job.pure b

private def checkPassive : FetchM Unit := do
  unless (paths (← PaperLean.BuildData.leanEnvFor (← getBuildContext))).isEmpty do
    error "passive runner borrowed active packs"
  unless (paths (← PaperLean.BuildEnv.leanEnv)).isEmpty do error "ambiguous legacy fetch"

private def checkOuter (ws : Workspace) (mod : Lake.Module) : FetchM (Job FilePath) := do
  let outer ← getBuildContext
  let marker := (ws.dir / "outer-marker").toString
  PaperLean.BuildEnv.addPack marker
  readHash outer (ws.dir / "outer.hash")
  let a ← makePack outer ws mod
  let b ← ws.runBuild (checkInner ws mod outer a marker)
  if ← b.pathExists then error "inner pack outlived its owner"
  unless ← a.pathExists do error "inner finish unlinked the live outer pack"
  unless (paths (← PaperLean.BuildEnv.leanEnv)).contains marker do error "outer environment was cleared"
  let bytes ← IO.FS.readBinFile (PaperLean.HashCache.recordFile ws.dir)
  IO.FS.writeBinFile (ws.dir / "inner-record") bytes
  ws.runFetchM checkPassive
  unless ← ws.checkNoBuild (do checkPassive; return Job.pure ()) do error "passive check failed"
  return Job.pure a

script ownership do
  let ws ← getWorkspace
  let some mod := ws.findModule? `Probe | error "missing Probe"
  PaperLean.BuildEnv.addPack "standalone"
  unless (paths (← PaperLean.BuildEnv.leanEnv)).contains "standalone" do error "standalone pack unavailable"
  PaperLean.BuildData.finish
  if (paths (← PaperLean.BuildEnv.leanEnv)).contains "standalone" then error "standalone finish left a pack"
  let a ← ws.runBuild (checkOuter ws mod)
  if ← a.pathExists then error "outer pack outlived its owner"
  let hot := PaperLean.HashCache.recordFile ws.dir
  let kept := PaperLean.HashCache.keptFile ws.dir
  let beforeHot ← IO.FS.readBinFile hot
  let beforeKept ← (IO.FS.readBinFile kept).toBaseIO
  ws.runBuild (pure (Job.pure ()))
  unless (← IO.FS.readBinFile hot) == beforeHot do error "empty build rotated its hash record"
  unless (← (IO.FS.readBinFile kept).toBaseIO).toOption == beforeKept.toOption do
    error "empty build changed its kept hash record"
  return 0
LEAN
run lake run ownership
grep -aq 'inner.hash' inner-record || fail "inner hash was not recorded"
! grep -aq 'outer.hash' inner-record || fail "inner record contains an outer read"
REC=.lake/paperlean-hashes.paperlean
grep -aq 'outer.hash' "$REC" || fail "outer hash was not recorded"
! grep -aq 'inner.hash' "$REC" || fail "outer record contains an inner read"
