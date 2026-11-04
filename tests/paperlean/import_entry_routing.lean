import Lean

/-!
How the import routes the extension entries of the parts of modules to their extensions, by the real
importer: the exported, server and private views of `module` files, legacy files, imports of IR
signatures only, a persistent environment, and an extension registered during another extension's
import callback, whose entries are routed before its own callback runs. The module data is written to
`_tmp_importEntryRouting` in the working directory. Run by `import_regressions.sh`.
-/

open Lean

private def check [BEq α] [Repr α] (label : String) (actual expected : α) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError s!"{label}: got {repr actual}, expected {repr expected}"

private unsafe def eraseEntries {α : Type} (xs : Array α) : Array EnvExtensionEntry :=
  unsafeCast xs

private unsafe def entries (offset row : Nat) : Array (Name × Array EnvExtensionEntry) :=
  match row with
  | 0 => #[
      (`RoutingFixture.nat, eraseEntries #[offset + 10]),
      (`RoutingFixture.text, eraseEntries #[s!"{offset}:a"]),
      (`RoutingFixture.unknown, eraseEntries #[999]),
      (`RoutingFixture.nat, eraseEntries #[offset + 11]),
      (`RoutingFixture.late, eraseEntries #[offset + 71])]
  | 1 => #[
      (`RoutingFixture.text, eraseEntries #["overwritten"]),
      (`RoutingFixture.text, eraseEntries (#[] : Array String))]
  | _ => #[
      (`RoutingFixture.nat, eraseEntries #[offset + 31, offset + 32]),
      (`RoutingFixture.late, eraseEntries #[offset + 73, offset + 74])]

private unsafe def moduleData (offset row : Nat) (imports : Array Import) : ModuleData :=
  { isModule := true, imports, constNames := #[], constants := #[], extraConstNames := #[],
    entries := entries offset row }

private unsafe def saveFixture (dir : System.FilePath) (modern := true) : IO (NameMap ImportArtifacts) := do
  IO.FS.createDirAll dir
  let mut arts : NameMap ImportArtifacts := {}
  let names := #[`RoutingFixture.A, `RoutingFixture.B, `RoutingFixture.C]
  for row in [:names.size] do
    let mod := names[row]!
    let imports := if row == 0 then #[] else
      #[{ module := names[row - 1]!, isExported := true, isMeta := true }]
    let base := dir / s!"{row}"
    let main := base.withExtension "olean"
    let server := base.withExtension "olean.server"
    let priv := base.withExtension "olean.private"
    let irSig := base.withExtension "ir.sig"
    let ir := base.withExtension "ir"
    if !modern then
      saveModuleDataParts mod #[(main, { moduleData 100 row imports with isModule := false })]
      arts := arts.insert mod (.ofArrays #[#[main], #[]])
      continue
    saveModuleDataParts mod #[
      (main, moduleData 100 row imports),
      (server, moduleData 200 row imports),
      (priv, moduleData 300 row imports)]
    saveModuleDataParts (mod ++ `ir) #[
      (irSig, moduleData 400 row imports),
      (ir, moduleData 500 row imports)]
    arts := arts.insert mod (.ofArrays #[#[main, server, priv], #[irSig, ir]])
  return arts

private def register (name : Name) (initial final : Nat) :
    IO (PersistentEnvExtension α α Nat) :=
  registerPersistentEnvExtension {
    name, mkInitial := pure initial, addImportedFn := fun _ => pure final,
    addEntryFn := fun s _ => s, exportEntriesFn := fun _ => #[] }

private def expectedNat (offset row : Nat) : Array Nat :=
  if row == 0 then #[offset + 11] else if row == 1 then #[] else #[offset + 31, offset + 32]

private def checkViews (env : Environment) (natExt : PersistentEnvExtension Nat Nat Nat)
    (textExt : PersistentEnvExtension String String Nat) (emptyExt : PersistentEnvExtension Nat Nat Nat)
    (mainOffset serverOffset : Nat) (irOffset := 500) : IO Unit := do
  check "all module rows" (natExt.toEnvExtension.getState (asyncMode := .sync) env).importedEntries.size 3
  check "empty extension retains all rows"
    (emptyExt.toEnvExtension.getState (asyncMode := .sync) env).importedEntries.size 3
  let names := #[`RoutingFixture.A, `RoutingFixture.B, `RoutingFixture.C]
  for row in [:names.size] do
    let some idx := env.getModuleIdx? names[row]! | throw <| IO.userError "missing module index"
    check "topological index" idx.toNat row
    check "main Nat entries" (natExt.getModuleEntries env idx) (expectedNat mainOffset row)
    check "server Nat entries" (natExt.getModuleEntries env idx (level := .server))
      (expectedNat serverOffset row)
    check "IR Nat entries" (natExt.getModuleIREntries env idx) (expectedNat irOffset row)
    check "main String entries" (textExt.getModuleEntries env idx)
      (if row == 0 then #[s!"{mainOffset}:a"] else #[])
    check "server String entries" (textExt.getModuleEntries env idx (level := .server))
      (if row == 0 then #[s!"{serverOffset}:a"] else #[])
    check "IR String entries" (textExt.getModuleIREntries env idx)
      (if row == 0 then #[s!"{irOffset}:a"] else #[])
    check "absent main entries" (emptyExt.getModuleEntries env idx) #[]
    check "absent IR entries" (emptyExt.getModuleIREntries env idx) #[]
    check "absent server entries" (emptyExt.getModuleEntries env idx (level := .server)) #[]

unsafe def main : IO Unit := do
  let dir : System.FilePath := "_tmp_importEntryRouting"
  let parallel := true
  let opts := ({} : Options).setBool `importModules.parallelEntries parallel
  let (natExt, textExt, emptyExt) ← withImporting do
    let natExt ← register (α := Nat) `RoutingFixture.nat 17 1517
    let textExt ← register (α := String) `RoutingFixture.text 29 1629
    let emptyExt ← register (α := Nat) `RoutingFixture.empty 43 1643
    return (natExt, textExt, emptyExt)
  let arts ← saveFixture dir
  let imports : Array Import := #[{ module := `RoutingFixture.C, isExported := true, isMeta := true }]
  for level in #[OLeanLevel.exported, .server, .private] do
    let env ← importModules imports opts (level := level) (arts := arts)
    try
      checkViews env natExt textExt emptyExt
        (if level == .private then 300 else 100)
        (if level == .private then 300 else if level == .server then 200 else 100)
      check "Nat initial state preserved" (natExt.getState env) 17
      check "String initial state preserved" (textExt.getState env) 29
      check "empty initial state preserved" (emptyExt.getState env) 43
    finally
      env.freeRegions
  let legacyArts ← saveFixture (dir / "legacy") false
  let legacy ← importModules imports opts (arts := legacyArts)
  try checkViews legacy natExt textExt emptyExt 100 100 100 finally legacy.freeRegions
  let irSig ← withImporting do
    let (_, state) ← importModulesCore (globalLevel := .exported) (loadIRSig := true) imports arts |>.run
    finalizeImport state imports opts (level := .exported) (loadIRSig := true)
      (leakEnv := false) (loadExts := false)
  try checkViews irSig natExt textExt emptyExt 100 100 400 finally irSig.freeRegions
  let persistent ← importModules imports opts (arts := arts) (leakEnv := true)
  checkViews persistent natExt textExt emptyExt 300 300
  let emptyEnv ← importModules #[] opts
  try
    check "zero imported modules" (natExt.toEnvExtension.getState (asyncMode := .sync) emptyEnv).importedEntries.size 0
  finally
    emptyEnv.freeRegions
  -- Register an extension during another extension's callback. Its serialized entries were
  -- ignored in the first pass and must be routed by the startingAt suffix pass before its callback.
  let lateRef ← IO.mkRef (none : Option (PersistentEnvExtension Nat Nat Nat))
  let _ ← withImporting <| registerPersistentEnvExtension (α := Nat) (β := Nat) (σ := Nat) {
    name := `RoutingFixture.trigger, mkInitial := pure 0,
    addImportedFn := fun _ => do
      let late ← liftM (m := IO) <| registerPersistentEnvExtension {
        name := `RoutingFixture.late, mkInitial := pure 47,
        addImportedFn := fun rows => pure (rows.foldl (fun n row => n + row.size) 0),
        addEntryFn := fun s _ => s, exportEntriesFn := fun _ => #[] }
      liftM (m := IO) <| lateRef.set (some late)
      return 77,
    addEntryFn := fun s _ => s, exportEntriesFn := fun _ => #[] }
  enableInitializersExecution
  let env ← importModules imports opts (loadExts := true) (level := .private) (arts := arts)
  -- Do not free regions after loadExts: initializer results may retain imported objects.
  checkViews env natExt textExt emptyExt 300 300
  check "normal callback ran" (natExt.getState env) 1517
  let some late ← lateRef.get | throw <| IO.userError "late extension was not registered"
  check "late callback saw routed entries" (late.getState env) 3
  let some idx := env.getModuleIdx? `RoutingFixture.A | throw <| IO.userError "missing module"
  check "late module index preserved" (late.getModuleEntries env idx) #[371]
  IO.println "import entry routing passed"
  IO.FS.removeDirAll dir
