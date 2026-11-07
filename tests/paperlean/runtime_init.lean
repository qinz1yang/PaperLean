import Lake.Load.Workspace
import Lake.Build.InitFacets
import Lake.Build.Infos
import Lake.PaperLean.BuildEnv
import Lake.PaperLean.BuildData
import Lake.PaperLean.BuiltinFacets
import Lake.PaperLean.HashCache
import Lake.PaperLean.Schedule
import Lake.PaperLean.SetupIndex
import Lake.PaperLean.SourceInputs
import Lake.PaperLean.SourceInputScope

open Lake Lean System
open Lake.PaperLean

private def ensure (p : Bool) (msg : String) : IO Unit := unless p do throw <| IO.userError msg

-- A TOML workspace requires no dynamically loaded Lake configuration plugin.
def main : IO Unit := do
  let dir ← IO.currentDir
  let (elan?, some lean, some lake) ← findInstall? | throw <| IO.userError "incomplete toolchain"
  let env ← IO.ofExcept (← (Lake.Env.compute lake lean elan?).toBaseIO)
  let some ws ← (loadWorkspaceRoot {lakeEnv := env, wsDir := dir}).toBaseIO
    | throw <| IO.userError "could not load TOML workspace"
  let ctx : BuildContext := {opaqueWs := ws, leanTrace := .nil "test", leanIncludeDirs := #[], registeredJobs := ← mkJobQueue}
  let other := {ctx with registeredJobs := ← mkJobQueue}
  let some facetMap ← builtinFacetMap.get | throw <| IO.userError "builtin facet hook did not run"
  ensure ((facetMap.get? Module.inputFacet).isSome) "missing builtin input facet"

  BuildEnv.clear
  BuildEnv.addPack "registry-pack"
  ensure ((← BuildEnv.leanEnv).any (·.2 == some "registry-pack")) "standalone pack was not retained"
  BuildData.startFor ctx dir false
  BuildData.startFor other dir false
  ensure (!(← BuildData.leanEnvFor ctx).any (·.2 == some "registry-pack")) "passive run borrowed a pack"
  BuildData.finishFor other
  BuildData.finishFor ctx
  BuildData.finish
  ensure (!(← BuildEnv.leanEnv).any (·.2 == some "registry-pack")) "retired pack survived"

  let mutex ← BuildMutex.new (1 : Nat)
  mutex.atomically do modify (·+2)
  ensure ((← mutex.get) == 3) "new runtime mutex did not protect state"
  let own ← BuildSessions.new (α := Nat)
  ensure (← own.insertFresh ctx 1) "first owner was not inserted"
  ensure (!(← own.insertFresh ctx 2)) "existing owner was replaced"
  ensure ((← own.find? ctx) == some 1 && (← own.find? other).isNone) "owners were not isolated"

  let scheduled ← Schedule.startFor ctx dir true
  ensure scheduled.active "scheduler did not start"
  ensure (!(← Schedule.sessionFor other).active) "scheduler leaked to another run"
  Schedule.finishFor ctx scheduled
  ensure (!(← Schedule.active)) "retired scheduler survived"
  HashCache.startFor ctx dir false
  discard <| HashCache.loadFor? ctx (dir / "missing.hash")
  HashCache.finishFor ctx
  HashCache.finish
  SetupIndex.beginRun ctx ws true
  ensure (← SetupIndex.observesProviders ctx) "canonical workspace did not admit providers"
  ensure (!(← SetupIndex.observesProviders other)) "setup witness leaked to another run"
  SetupIndex.endRun ctx
  ensure (!(← SetupIndex.observesProviders ctx)) "retired setup witness survived"
  ensure (← SetupIndex.moved).isEmpty "standalone setup state was not empty"
  SourceInputScope.withRun ctx true do
    discard <| SourceInputs.selectRead ctx (dir / "Fixture.lean")
  IO.println "runtime registries initialized"
