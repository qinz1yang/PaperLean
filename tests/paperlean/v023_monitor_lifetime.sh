# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# A returned target can register jobs after the outer fetch has already completed.
cd "$TMP_DIR"
export PAPERLEAN_ACCELERATE=1 PAPERLEAN_HASH_CACHE=0 PAPERLEAN_SCHEDULE=0
cat > lakefile.lean <<'LEAN'
import Lake
import Lake.PaperLean.BuildData
import Lake.PaperLean.BuildEnv
open Lake DSL

package MonitorLifetime

private def runCase (ws : Workspace) (fail failFast : Bool) (failTarget logTarget := false) : IO Unit := do
  let observed ← IO.mkRef false
  let canceled ← IO.mkRef false
  let childDone ← IO.Promise.new
  let watcherDone ← IO.Promise.new
  let succeeded ← try
    ws.runBuild (cfg := {failFast}) do
      let ctx ← getBuildContext
      let marker := (ws.dir / "sentinel.pack").toString
      PaperLean.BuildEnv.addPack marker
      let inner : JobTask Unit ← BaseIO.asTask (prio := .dedicated) do
        IO.sleep 120
        let child : JobTask Unit ← BaseIO.asTask (prio := .dedicated) do
          IO.sleep 100
          let vars ← PaperLean.BuildData.leanEnvFor ctx
          let packs := (vars.find? (·.1 == "LEAN_OLEAN_PACK")).bind Prod.snd
          observed.set (packs.any fun s => marker ∈ s.splitOn ":")
          childDone.resolve ()
          if fail then return .error 0 {log := ⟨#[.error "expected late failure"]⟩}
          return .ok () {}
        ctx.registeredJobs.modify (·.push (Job.ofTask child "late child"))
        if failFast then
          let watcher : JobTask Unit ← BaseIO.asTask (prio := .dedicated) do
            if let some token := ctx.cancelTk? then
              for _ in [0:200] do
                if ← token.isSet then break
                IO.sleep 10
              canceled.set (← token.isSet)
            watcherDone.resolve ()
            return .ok () {}
          ctx.registeredJobs.modify (·.push (Job.ofTask watcher "cancellation watcher"))
        if logTarget then return .ok () {log := ⟨#[.error "expected target diagnostic"]⟩}
        if failTarget then return .error 0 {log := ⟨#[.error "expected target failure"]⟩}
        return .ok () {}
      return Job.ofTask inner
    pure true
  catch _ => pure false
  discard <| IO.wait childDone.result?
  if failFast then discard <| IO.wait watcherDone.result?
  unless ← observed.get do throw <| IO.userError "run resources retired before the late child's completion"
  if succeeded == (fail || failTarget || logTarget) then throw <| IO.userError "late required failure was reported incorrectly"
  if failFast && !(← canceled.get) then throw <| IO.userError "late failure did not cancel sibling"

script lifetime do
  let ws ← getWorkspace
  runCase ws false false
  runCase ws true false
  runCase ws true true
  runCase ws false true true
  runCase ws false true false true
  return 0
LEAN
run lake run lifetime
