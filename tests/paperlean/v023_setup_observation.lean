/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake.PaperLean.SetupProviders
import Lake.Config.Workspace

open Lean Lake Lake.PaperLean.SetupProviders

private def pkg : Package := {(default : Package) with wsIdx := 0, depIdxs := #[]}
private def raw : Workspace.Raw := {
  lakeEnv := default, lakeCache := default, packages := #[pkg]
  lakeConfig := {config := default, defaultCacheService := .reservoirService "", defaultCacheUploadService? := none, cacheServices := {}}
}
private def ws : Workspace := { raw with
  size_packages_pos := by simp [raw]
  packages_wsIdx := by
    intro i h
    have hi : i < 1 := h
    have hi : i = 0 := by omega
    subst i
    rfl
  depIdxs_packages := by intro p hp i hi; simp [raw] at hp; subst p; simp [pkg] at hi
}
private def lib : LeanLib := {pkg, name := `Test, config := {}}
private def mod (name : Name) : Lake.Module := {name, lib}
private def input (children : Array Lake.Module) : ModuleInput := {
  path := "input", trace := .nil, header := {imports := #[], isModule := true}
  imports := children.map fun m => {module := m.name, module? := some m}
}
private def saveInput (ctx : BuildContext) (store : IO.Ref BuildStore) (m : Lake.Module)
    (job : Job ModuleInput) : IO Unit := do
  let raw : Job (BuildData m.input.key) := cast (by simp) job
  let selected ← storeJob ctx store m.input raw
  unless unsafe ptrEq raw.task selected.task do throw <| IO.userError "a selected input acquired a wrapper"
  checkResult ctx store m.input selected

private def saveExport (ctx : BuildContext) (store : IO.Ref BuildStore) (m : Lake.Module)
    (job : Job ModuleExportInfo) : IO Unit := do
  let raw : Job (BuildData m.exportInfo.key) := cast (by simp) job
  let selected ← storeJob ctx store m.exportInfo raw
  unless unsafe ptrEq raw.task selected.task do throw <| IO.userError "a selected export acquired a wrapper"
  checkResult ctx store m.exportInfo selected

def main : IO Unit := do
  let ctx : BuildContext := {opaqueWs := ws, registeredJobs := ← mkJobQueue, leanTrace := .nil, leanIncludeDirs := #[]}
  let store ← IO.mkRef BuildStore.empty
  let inputs ← IO.mkRef (#[] : Array Name)
  let exports ← IO.mkRef (#[] : Array (Name × String))
  let root := mod `Root
  let middle := mod `Middle
  let leaf := mod `Leaf
  let unused := mod `Unused
  let fetch ← IO.mkRef ()
  beginRun ctx true (fun _ => true) {
    input := fun m _ => inputs.modify (·.push m.name)
    exports := fun m e => exports.modify (·.push (m.name, e.arts.olean?.map (·.toString) |>.getD ""))
  }
  for m in #[root, middle, leaf, unused] do enterProvider ctx store m.leanArts fetch true
  saveInput ctx store root (.pure (input #[middle]))
  saveInput ctx store middle (.pure (input #[leaf]))
  saveInput ctx store leaf (.pure (input #[]))
  let pending : IO.Promise (JobResult ModuleExportInfo) ← IO.Promise.new
  saveExport ctx store middle (.ofTask (pending.resultD (.error 0 {})))
  let leafExport := {(default : ModuleExportInfo) with arts := .ofArrays #[#["moved/Leaf.olean"]]}
  saveExport ctx store leaf (.pure leafExport)
  let unresolved : IO.Promise (JobResult ModuleInput) ← IO.Promise.new
  saveInput ctx store unused (.ofTask (unresolved.resultD (.error 0 {})))
  unless (← inputs.get).isEmpty && (← exports.get).isEmpty do
    throw <| IO.userError "memoization ran observers without a setup"
  unless ← prepareStored ctx root do throw <| IO.userError "explicit input-only graph was not ready"
  unless (← exports.get).isEmpty do throw <| IO.userError "the input-only query read an export"
  if ← mayIndex ctx store fetch root then throw <| IO.userError "pending imported export was ignored"
  pending.resolve (.ok {(default : ModuleExportInfo) with arts := .ofArrays #[#["moved/Middle.olean"]]} {})
  let some selected := (← store.get).get? middle.exportInfo.key | throw <| IO.userError "missing selected export"
  discard <| IO.wait selected.task
  unless ← mayIndex ctx store fetch root do throw <| IO.userError "completed export did not unblock the graph"
  unless ← mayIndex ctx store fetch root do throw <| IO.userError "certified graph was lost"
  unless (← inputs.get) == #[root.name, middle.name, leaf.name] do throw <| IO.userError "wrong or duplicate input observations"
  unless (← exports.get) == #[(middle.name, "moved/Middle.olean"), (leaf.name, "moved/Leaf.olean")] do
    throw <| IO.userError "an export was lost, duplicated or observed before it was ready"
  unresolved.resolve (.error 0 {})
  if ← prepareStored ctx unused then throw <| IO.userError "failed input was admitted"
  endRun ctx
  IO.println "selected inputs and exports observed only on demand"
