/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
import all Lean.Environment
import Lean.PaperLean.Base
import Lean.PaperLean.GraphDiff
import Lean.Compiler.ModPkgExt
import Lean.Compiler.NameMangling
import Lean.Compiler.InitAttr

/-!
The faster steps of `Lean.importModules`, which `Lean.Environment` calls through `@[extern]` hooks
(`paperleanImportModules` etc.). Each step produces exactly the objects of Lean's code for it, which
the hook passes as an argument: `PAPERLEAN_IMPORT=legacy` runs only Lean's code, and
`PAPERLEAN_IMPORT=check` runs both and fails the import if their results differ in any object.
-/

namespace Lean
open PaperLean

private def checkSameAsLegacy {α : Type} (what : String) (legacy fast : α) : IO Unit := do
  if let some d := unsafe PaperLean.graphDiff legacy fast true then
    throw <| IO.userError s!"PAPERLEAN_IMPORT=check: {what} differs from the legacy import: {d}"

/--
For each name of `extNames`, the `importedEntries` that `setImportedEntries` builds for the
extension of that name: per module, the entries of the last element of `mod.entries` with that
name, or `empty`. With `persistent`, the arrays may be allocated persistent.
-/
@[extern "lean_paperlean_imported_entries_arrays"]
private opaque importedEntriesArrays (mods : @& Array ModuleData) (extNames : @& Array Name)
    (empty : @& Array EnvExtensionEntry) (persistent : Bool) : Array (Array (Array EnvExtensionEntry))

/-- `setImportedEntries`, building each `importedEntries` array at once. -/
private def setImportedEntriesFast (states : Array EnvExtensionState) (mods : Array ModuleData)
    (startingAt : Nat) (persistent : Bool) : IO (Array EnvExtensionState) := do
  let mut states := states
  let descrs := (← persistentEnvExtensionsRef.get)[startingAt...*].toArray
  let arrays := importedEntriesArrays mods (descrs.map (·.name)) PaperLean.noImportedEntries persistent
  for h : i in *...descrs.size do
    let entries := arrays[i]!
    -- safety: as in `modifyState`
    states := unsafe descrs[i].toEnvExtension.modifyStateImpl states fun s =>
      { s with importedEntries := entries }
  return states

/--
Starts building the imported state of the extension named `extName` from the entries `as` on
another thread, if it is replayed and the import image has most of its entries
(`Lean.PaperLean.ImportState`, `src/paperlean/import_state.cpp`); `ScopedEnvExtension.addImportedFn`
takes the state if it gets the same entries. Called from `finalizePersistentExtensions`, which
calls `addImportedFn` for every extension.
-/
@[extern "lean_paperlean_prefetch_imported_state"]
private opaque prefetchImportedState (extName : @& Name) (as : @& Array (Array EnvExtensionEntry))
    (persistent : Bool) : BaseIO Unit

@[export lean_paperlean_set_imported_entries]
private def setImportedEntriesImpl (states : Array EnvExtensionState) (mods : Array ModuleData)
    (startingAt : Nat) (persistent : Bool) (core : Unit → IO (Array EnvExtensionState)) :
    IO (Array EnvExtensionState) := do
  let mode ← importMode
  if mode == 1 then return (← core ())
  let fast ← setImportedEntriesFast states mods startingAt persistent
  if mode == 2 then
    let legacy ← core ()
    for descr in (← persistentEnvExtensionsRef.get)[startingAt...*] do
      let l := unsafe descr.toEnvExtension.getStateImpl legacy
      let f := unsafe descr.toEnvExtension.getStateImpl fast
      -- the states themselves are not changed
      unless unsafe ptrEq l.state f.state do
        throw <| IO.userError s!"PAPERLEAN_IMPORT=check: the state of {descr.name} differs from the legacy import"
      checkSameAsLegacy s!"`importedEntries` of {descr.name}" l.importedEntries f.importedEntries
  importTimingMark "entries"
  return fast

/-- Waits for the replays of `prefetchImportedState` of this thread that were not taken and releases them. -/
@[extern "lean_paperlean_drop_prefetched_replays"]
private opaque dropPrefetchedReplays (env : @& Environment) : BaseIO Unit

/--
The extensions whose `addImportedFn` is a pure function of their entries and of the environment's
header, so that it can run before the extensions registered before them are finalized.
-/
private def pureImportedFolds : Array String := #[
  "_private.Lean.Compiler.LCNF.Specialize.0.Lean.Compiler.LCNF.Specialize.specCacheExt",
  "_private.Lean.Namespace.0.Lean.namespacesExt",
  "Lean.Meta.Match.Extension.extension"]

/-- The results of `addImportedFn` that `prefetchImportedStates` computes in the background. -/
private builtin_initialize importedFoldsRef :
    IO.Ref (Array (Name × Array (Array EnvExtensionEntry) × Task (Except IO.Error EnvExtensionState))) ←
  IO.mkRef #[]

/--
Loads the native libraries of `PAPERLEAN_NATIVE_LIBS` that are verified for imported modules of `env`
(`src/paperlean/native_libs.cpp`) before the interpreter first runs for `env`, and starts using them
for those modules of `env` on this thread until `endNativeInit`. Does nothing, and allocates nothing,
if the variable is not set.
-/
@[extern "lean_paperlean_load_native_libs"]
private opaque loadNativeLibs (env : @& Environment) (opts : @& Options) : BaseIO Unit

/-- What `loadNativeLibs` needs to know about the imported modules of an environment, by module index. -/
private structure NativeImportInfo where
  names : Array Name
  /-- Whether `runInitAttrForMod` runs the module's runtime initializer, not only its compile-time
  initializer. -/
  runtimeInit : Array Bool
  /-- Whether the module has `[init]` declarations that its runtime initializer runs: those not
  marked `meta` in a `module`, all of them otherwise, whose initializers run every phase. -/
  hasInit : Array Bool
  /-- The name of the module's initializer for all phases; those for run time and compile time add
  a prefix (`mkModuleInitializationFunctionName`). -/
  inits : Array String
  /-- Its direct imports: twice the module index (`names.size` for a module that is not imported),
  plus one for a `meta import` in a `module` (otherwise initializers run every phase). -/
  imports : Array (Array Nat)

@[export lean_paperlean_native_import_info]
private def nativeImportInfo (env : Environment) (opts : Options) : NativeImportInfo :=
  let isModule := env.header.isModule
  let inServer := opts.getBool `Elab.inServer
  let mods := env.header.modules
  { names := env.header.moduleNames
    runtimeInit := mods.map fun mod => !isModule || inServer || mod.irPhases != .runtime
    hasInit := mods.mapIdx fun idx _ =>
      let runtime := fun ((decl, _) : Name × Name) => !isModule || !isMarkedMeta env decl
      (regularInitAttr.ext.getModuleEntries env idx).any runtime ||
        (regularInitAttr.ext.getModuleIREntries env idx).any runtime
    inits := mods.mapIdx fun idx mod =>
      mkModuleInitializationFunctionName mod.module (env.getModulePackageByIdx? idx)
    imports := env.header.moduleData.map fun d =>
      d.imports.map fun i =>
        2 * ((env.getModuleIdx? i.module).map (·.toNat)).getD mods.size + if isModule && i.isMeta then 1 else 0 }

/-- Whether `n` is marked `meta` in `env`; then a module's compile-time initializer initializes it. -/
@[export lean_paperlean_is_meta_const]
private def isMetaConst (env : Environment) (n : Name) : Bool := isMarkedMeta env n

/-- The module index of the imported constant `n` of `env` plus one, `0` if `n` is not imported. -/
@[export lean_paperlean_const_module_idx]
private def constModuleIdx (env : Environment) (n : Name) : UInt32 :=
  match env.getModuleIdxFor? n with
  | some idx => idx.toUInt32 + 1
  | none => 0

/-- Ends the use of the native module initializers that `loadNativeLibs` allowed for `env`. -/
@[extern "lean_paperlean_end_native_init"]
private opaque endNativeInit (env : @& Environment) : BaseIO Unit

@[export lean_paperlean_prefetch_imported_states]
private def prefetchImportedStatesImpl (env : Environment) (opts : Options) (startingAt : Nat)
    (persistent : Bool) : BaseIO Unit := do
  if (← importMode) == 1 then return
  -- before the interpreter first runs for `env`
  if startingAt == 0 then
    loadNativeLibs env opts
  let states := env.base.private.extensions
  for descr in (← persistentEnvExtensionsRef.get)[startingAt...*] do
    let as := (unsafe descr.toEnvExtension.getStateImpl states).importedEntries
    prefetchImportedState descr.name as persistent
    -- only in an environment marked persistent, which the task does not need to mark
    if persistent && pureImportedFolds.contains descr.name.toString then
      let task ← IO.asTask (descr.addImportedFn as { env, opts }) .dedicated
      importedFoldsRef.modify (·.push (descr.name, as, task))

/-- The result of `addImportedFn` of the extension named `extName` for the entries `as`, if it was
computed in the background. -/
private def takeImportedFold (extName : Name) (as : Array (Array EnvExtensionEntry)) :
    BaseIO (Option (Except IO.Error EnvExtensionState)) := do
  let folds ← importedFoldsRef.get
  let some i := folds.findIdx? fun (n, as', _) => n == extName && unsafe ptrEq as as' | return none
  importedFoldsRef.modify fun folds => folds.filter fun (_, as', _) => !unsafe ptrEq as as'
  return some (← IO.wait folds[i]!.2.2)

/--
Runs `act`, in which the outermost evaluations by the interpreter for `env` and `opts` share the
interpreter's symbol cache, which depends only on the environment (unless `PAPERLEAN_IMPORT=legacy`).
-/
@[extern "lean_paperlean_with_import_interpreter"]
private opaque withImportInterpreter {α : Type} [Nonempty α] (env : @& Environment) (opts : @& Options)
    (act : BaseIO α) : BaseIO α

@[export lean_paperlean_imported_extension_state]
private def importedExtensionStateImpl (extName : Name) (as : Array (Array EnvExtensionEntry))
    (env : Environment) (opts : Options) (fold : Unit → IO EnvExtensionState) : IO EnvExtensionState := do
  let result ← match ← takeImportedFold extName as with
    | some result => pure result
    | none => (withImportInterpreter env opts (fold ()).toBaseIO : BaseIO _)
  if ← importTimingEnabled then importTimingMark s!"ext {extName}"
  match result with
  | .ok state => pure state
  | .error e => throw e

@[export lean_paperlean_drop_prefetched_states]
private def dropPrefetchedStatesImpl (env : Environment) : BaseIO Unit := do
  endNativeInit env
  dropPrefetchedReplays env
  -- the folds of this environment's extensions that were not taken, which finish on their own
  let states := env.base.private.extensions
  let mine ← (← persistentEnvExtensionsRef.get).filterMapM fun descr => do
    if descr.toEnvExtension.idx < states.size then
      return some (unsafe descr.toEnvExtension.getStateImpl states).importedEntries
    return none
  importedFoldsRef.modify fun folds => folds.filter fun (_, as, _) => !mine.any (unsafe ptrEq · as)

/--
Resolves an imported constant `cinfo` whose name is already in `map` with `prev` as in
`finalizeImport`: `1` if `cinfo` replaces `prev`, `2` if the import fails (only if `checkError`),
`0` if `prev` stays.
-/
@[export lean_paperlean_import_resolve_duplicate]
private def resolveImportedDuplicate (map : Std.HashMap Name ConstantInfo) (cinfo prev : ConstantInfo)
    (checkError : Bool) : UInt8 :=
  if subsumesInfo map cinfo prev then 1
  else if checkError && !subsumesInfo map prev cinfo then 2
  else 0

/--
The private constant map and `const2ModIdx` that the fold in `finalizeImport` builds starting from
`emptyWithCapacity` of the given capacities; also the module index and name for which the fold
calls `throwAlreadyImported`, if any, in which case the maps are those at that point. `none` if the
capacities are out of range. With `persistent`, new objects may be allocated persistent.
-/
@[extern "lean_paperlean_build_private_constant_maps"]
private opaque buildPrivateConstantMaps (moduleData irData : @& Array ModuleData)
    (privateCapacity c2mCapacity : @& Nat) (persistent : Bool) :
    Option (Std.HashMap Name ConstantInfo × Std.HashMap Name ModuleIdx × Option (Nat × Name))

/-- The public constant map of `finalizeImport` for the given module data, as `buildPrivateConstantMaps`. -/
@[extern "lean_paperlean_build_public_constant_map"]
private opaque buildPublicConstantMap (datas : @& Array ModuleData) (capacity : @& Nat)
    (persistent : Bool) : Option (Std.HashMap Name ConstantInfo)


/--
The private constant map and `const2ModIdx` of `finalizeImport` built faster, with the module index
and name for which its fold calls `throwAlreadyImported`, if any; `none` if `finalizeImport` builds
them by its fold (`PAPERLEAN_IMPORT=legacy`, or capacities out of range).
-/
@[export lean_paperlean_private_constant_maps]
private def privateConstantMapsImpl (moduleData irData : Array ModuleData)
    (privateCapacity c2mCapacity : Nat) (persistent : Bool) :
    IO (Option (Std.HashMap Name ConstantInfo × Std.HashMap Name ModuleIdx × Option (Nat × Name))) := do
  let r := if (← importMode) == 1 then none else
    buildPrivateConstantMaps moduleData irData privateCapacity c2mCapacity persistent
  importTimingMark "constants.private"
  return r

/-- `PAPERLEAN_IMPORT=check`: fails if the maps built faster differ from those of the fold, which
did not fail. -/
@[export lean_paperlean_check_private_constant_maps]
private def checkPrivateConstantMapsImpl
    (fast : Std.HashMap Name ConstantInfo × Std.HashMap Name ModuleIdx × Option (Nat × Name))
    (privateConstantMap : Std.HashMap Name ConstantInfo) (const2ModIdx : Std.HashMap Name ModuleIdx) :
    IO Unit := do
  if fast.2.2.isSome then throw <| IO.userError "PAPERLEAN_IMPORT=check: only the fast import fails"
  checkSameAsLegacy "the private constant map" privateConstantMap fast.1
  checkSameAsLegacy "`const2ModIdx`" const2ModIdx fast.2.1

/-- The public constant map of `finalizeImport` built faster; `none` if `finalizeImport` builds it by
its fold (`PAPERLEAN_IMPORT=legacy`, not a module, or capacity out of range). -/
@[export lean_paperlean_public_constant_map]
private def publicConstantMapImpl (modules : Array ImportedModule) (capacity : Nat)
    (isModule persistent : Bool) : IO (Option (Std.HashMap Name ConstantInfo)) := do
  let r := if (← importMode) == 1 || !isModule then none else
    let datas := modules.filterMap fun mod => if mod.isExported then mod.publicModule? else none
    buildPublicConstantMap datas capacity persistent
  importTimingMark "constants.public"
  return r

/-- `PAPERLEAN_IMPORT=check`: fails if the public constant map built faster differs from the fold's. -/
@[export lean_paperlean_check_public_constant_map]
private def checkPublicConstantMapImpl (fast fold : Std.HashMap Name ConstantInfo) : IO Unit :=
  checkSameAsLegacy "the public constant map" fold fast

/-!
`fastImportModules` computes the result of `importModulesCore` reading the modules of olean packs
(`LEAN_OLEAN_PACK`) from the packs' module tables instead of their `.olean` files: the imports of a
packed module come from the table, which also identifies the module, and its files are served from
the pack without searching for them. Other modules are read as in `importModulesCore`. When the
tables do not suffice it throws, and `importModules` uses `importModulesCore` instead.
-/

/-- The packed module named `name` whose imports are in its pack's table, if any (`noPackModule`). -/
@[extern "lean_paperlean_pack_module_find"]
private opaque packModuleFind (name : @& Name) : UInt32
/-- Whether some olean pack is in use. -/
@[extern "lean_paperlean_packs_loaded"]
private opaque packsLoaded : BaseIO Bool
/--
Starts checking, on other threads, whether the files of the packed modules reachable from `m` in its
pack's table changed since packing, so that serving them later need not wait for the check.
-/
@[extern "lean_paperlean_pack_prevalidate"]
private opaque packPrevalidate (m : UInt32) : BaseIO Unit
@[extern "lean_paperlean_pack_module_num_edges"]
private opaque packModuleNumEdges (m : UInt32) : UInt32
/-- The module imported by the `j`-th import of `m` if it is in the same pack (`noPackModule`). -/
@[extern "lean_paperlean_pack_module_edge_target"]
private opaque packModuleEdgeTarget (m j : UInt32) : UInt32
/-- The `j`-th import of `m`, with the fields of its `Import` object. -/
@[extern "lean_paperlean_pack_module_edge_import"]
private opaque packModuleEdgeImport (m j : UInt32) : Import
/-- `importAll`, `isExported` and `isMeta` of the `j`-th import of `m`, as bits 0, 1 and 2. -/
@[extern "lean_paperlean_pack_module_edge_flags"]
private opaque packModuleEdgeFlags (m j : UInt32) : UInt8
/-- The paths of the packed `.olean` and IR files of `m`, in their order in their chains. -/
@[extern "lean_paperlean_pack_module_paths"]
private opaque packModulePaths (m : UInt32) : Array String × Array String
/-- The root of the files of `m` and its package (the first component of its name). -/
@[extern "lean_paperlean_pack_module_package"]
private opaque packModulePackage (m : UInt32) : String × String
@[extern "lean_paperlean_pack_module_is_module"]
private opaque packModuleIsModule (m : UInt32) : Bool
/-- The first `count` parts of the `.olean` (or IR) chain of `m`, if they can be served. -/
@[extern "lean_paperlean_pack_module_parts"]
private opaque packModuleParts (m : UInt32) (ir : Bool) (count : UInt32) :
    BaseIO (Option (Array (ModuleData × CompactedRegion)))

private def noPackModule : UInt32 := 0xffffffff

deriving instance Inhabited for ImportedModule

private structure FastImportState where
  records : Array ImportedModule := #[]
  /-- Indices into `records` in the order of `ImportState.moduleNames`. -/
  order : Array Nat := #[]
  byPack : Std.HashMap UInt32 Nat := {}
  byName : Std.HashMap Name Nat := {}
  /-- For packed modules found via the search path: whether the search path finds their package
  in their pack root, by pack root and package (`root/package`). -/
  packageRoots : Std.HashMap String Bool := {}
  /-- The regions read from files, to be freed if the traversal is abandoned. -/
  read : List CompactedRegion := []
  /-- The result of `readIRPartsOfMod` for modules without IR files. `importModulesCore` reads
  them again at every later import of such a module, with the same result. -/
  noIR : Std.HashMap Name (Array (ModuleData × CompactedRegion)) := {}

private abbrev FastImportM := StateRefT FastImportState IO

private def fastImportFail {α} (why : String) : FastImportM α :=
  throw <| IO.userError s!"fast import not applicable: {why}"

/-- Whether `importModulesCore` reads packed module `m` from the files of its pack: from `arts`,
`artsOf` holds the artifacts of the packed modules that have them, and the search path must find the
module's package in the module's pack root. -/
private def packModuleServable (m : UInt32) (artsOf : Std.HashMap UInt32 ImportArtifacts) :
    FastImportM Bool := do
  if artsOf.contains m then return true
  let (root, pkg) := packModulePackage m
  let dir := root ++ "/" ++ pkg
  if let some ok := (← get).packageRoots[dir]? then return ok
  let sp ← searchPathRef.get
  let ok := match ← sp.findWithExt "olean" (.mkSimple pkg) with
    | some p => p.toString == dir ++ ".olean"
    | none => false
  modify fun s => { s with packageRoots := s.packageRoots.insert dir ok }
  return ok

private partial def fastImportModules (imports : Array Import) (globalLevel : OLeanLevel)
    (arts : NameMap ImportArtifacts) (isExported : Bool) (artsOf : Std.HashMap UInt32 ImportArtifacts)
    (reuse : Option ImportState := none) : FastImportM Unit := do
  goArray imports (importAll := true) (isExported := isExported) (needsData := true) (needsIRTrans := false)
  if globalLevel < .private then
    for i in imports do
      if let some mod := (← lookup (← target i) i).bind (·.mainModule?) then
        if !mod.isModule then
          throw <| IO.userError s!"cannot import non-`module` {i.module} from `module`"
where
  target (i : Import) : FastImportM (Option UInt32) := do
    let m := packModuleFind i.module
    if m == noPackModule then return none
    packPrevalidate m
    return some m
  lookup (m? : Option UInt32) (i : Import) : FastImportM (Option ImportedModule) := do
    let s ← get
    let r? := match m? with
      | some m => s.byPack[m]?
      | none => s.byName[i.module]?
    return r?.map (s.records[·]!)
  goArray (imports : Array Import) (importAll isExported needsData needsIRTrans : Bool) :
      FastImportM Unit := do
    for i in imports do
      visit i (← target i) importAll isExported needsData needsIRTrans
  goPack (m : UInt32) (importAll isExported needsData needsIRTrans : Bool) : FastImportM Unit := do
    for j in 0...(packModuleNumEdges m).toNat do
      let j := j.toUInt32
      let t := packModuleEdgeTarget m j
      if t != noPackModule then
        unless ← unchanged (packModuleEdgeFlags m j) t importAll isExported needsData needsIRTrans do
          visit (packModuleEdgeImport m j) (some t) importAll isExported needsData needsIRTrans
      else
        let i := packModuleEdgeImport m j
        visit i (← target i) importAll isExported needsData needsIRTrans
  /-- Whether `visit` of an import with flags `f` (`packModuleEdgeFlags`) of the already recorded
  packed module `t` would do nothing. -/
  unchanged (f : UInt8) (t : UInt32) (importAll isExported needsData needsIRTrans : Bool) :
      FastImportM Bool := do
    let s ← get
    let some r := s.byPack[t]? | return false
    let mod := s.records[r]!
    -- as in `visit`
    let needsData := needsData && (f &&& 2 != 0 || importAll)
    let importAll := globalLevel == .private || importAll && f &&& 1 != 0
    let isExported := isExported && f &&& 2 != 0
    let needsIRTrans := needsIRTrans || (needsData && f &&& 4 != 0)
    let needsIR := needsIRTrans || importAll || globalLevel > .exported
    if !needsData && !needsIR then
      return true
    let irPhases :=
      if importAll then .all
      else if needsIRTrans then .comptime
      else .runtime
    let importAll := importAll || mod.importAll
    let isExported := isExported || mod.isExported
    let needsData := needsData || mod.hasData
    let needsIRTrans := needsIRTrans || mod.needsIRTrans
    let needsIR := needsIRTrans || importAll
    let irPhases := if irPhases == mod.irPhases then irPhases else .all
    return !(needsData && mod.parts.isEmpty) && !(needsIR && mod.irParts.isEmpty) &&
      importAll == mod.importAll && isExported == mod.isExported &&
      needsIRTrans == mod.needsIRTrans && needsData == mod.hasData && irPhases == mod.irPhases
  -- `go` of `importModulesCore`, for one import
  visit (i : Import) (m? : Option UInt32) (importAll isExported needsData needsIRTrans : Bool) :
      FastImportM Unit := do
    -- `B > none`?
    let needsData := needsData && (i.isExported || importAll)
    -- `B ≥ privateAll`?
    let importAll := globalLevel == .private || importAll && i.importAll
    -- `B ≥ public`?
    let isExported := isExported && i.isExported
    let needsIRTrans := needsIRTrans || (needsData && i.isMeta)
    let needsIR := needsIRTrans || importAll || globalLevel > .exported
    if !needsData && !needsIR then
      return
    let irPhases :=
      if importAll then .all
      else if needsIRTrans then .comptime
      else .runtime
    let goRec (mod : ImportedModule) : FastImportM Unit := do
      match m? with
      | some m =>
        -- `mod.mainModule?.isSome`, with the packed `isModule` of `mod.publicModule?`
        if mod.hasData then
          let level : OLeanLevel :=
            if packModuleIsModule m then (if mod.importAll then .private else .exported) else .exported
          if level.ctorIdx < mod.parts.size then
            -- the table holds the imports of the `.olean` parts
            goPack m (importAll := importAll) (isExported := isExported) (needsData := needsData) (needsIRTrans := needsIRTrans)
        else if let some (ir, _) := mod.irParts.back? then
          -- `mainModule?` of a module imported without data: its last IR part
          goArray (importAll := importAll) (isExported := isExported) (needsData := needsData) (needsIRTrans := needsIRTrans) ir.imports
      | none =>
        if let some data := mod.mainModule? then
          goArray (importAll := importAll) (isExported := isExported) (needsData := needsData) (needsIRTrans := needsIRTrans) data.imports
    let s ← get
    if let some r := (match m? with | some m => s.byPack[m]? | none => s.byName[i.module]?) then
      let mod := s.records[r]!
      -- when module is already imported, bump flags
      let importAll := importAll || mod.importAll
      let isExported := isExported || mod.isExported
      let needsData := needsData || mod.hasData
      let needsIRTrans := needsIRTrans || mod.needsIRTrans
      let needsIR := needsIRTrans || importAll
      let irPhases := if irPhases == mod.irPhases then irPhases else .all
      let parts ← if needsData && mod.parts.isEmpty then loadData i m? else pure mod.parts
      let irParts ← if needsIR && mod.irParts.isEmpty then loadIR i m? else pure mod.irParts
      if importAll != mod.importAll || isExported != mod.isExported ||
          needsIRTrans != mod.needsIRTrans || needsData != mod.hasData || irPhases != mod.irPhases then
        modify fun s => { s with records := s.records.set! r { mod with
          importAll, isExported, irPhases, parts, irParts, hasData := needsData, needsIRTrans }}
        -- bump entire closure
        goRec mod
      return
    -- newly discovered module
    let parts ← if needsData then loadData i m? else pure #[]
    let irParts ← if needsIR then loadIR i m? else pure #[]
    let mod : ImportedModule :=
      { i with importAll, isExported, irPhases, parts, irParts, needsIRTrans, hasData := needsData }
    goRec mod
    modify fun s =>
      let r := s.records.size
      { s with
        records := s.records.push mod
        order := s.order.push r
        byPack := if let some m := m? then s.byPack.insert m r else s.byPack
        byName := if m?.isNone then s.byName.insert i.module r else s.byName }
  reused (i : Import) (ir : Bool) : Option (Array (ModuleData × CompactedRegion)) := do
    let mod ← (← reuse).moduleNameMap[i.module]?
    let parts := if ir then mod.irParts else mod.parts
    guard !parts.isEmpty
    return parts
  noteRead (parts : Array (ModuleData × CompactedRegion)) : FastImportM (Array (ModuleData × CompactedRegion)) := do
    modify fun s => { s with read := parts.foldl (fun read part => part.2 :: read) s.read }
    return parts
  readIR (mod : Name) : FastImportM (Array (ModuleData × CompactedRegion)) := do
    if let some parts := (← get).noIR[mod]? then return parts
    let parts ← noteRead (← readIRPartsOfMod mod)
    if parts.isEmpty then modify fun s => { s with noIR := s.noIR.insert mod parts }
    return parts
  -- .olean + .olean.server (optional) + .olean.private (optional)
  loadData (i : Import) (m? : Option UInt32) : FastImportM (Array (ModuleData × CompactedRegion)) := do
    let some m := m? | do
      if let some parts := reused i false then return parts
      if let some arts := arts.find? i.module then
        noteRead (← readModuleDataParts (arts.oleanParts (inServer := globalLevel ≥ OLeanLevel.server)))
      else
        noteRead (← readModuleDataPartsOfMod i.module)
    unless ← packModuleServable m artsOf do fastImportFail s!"{i.module} is not read from its pack"
    let count := match artsOf[m]? with
      | some arts => (arts.oleanParts (inServer := globalLevel ≥ OLeanLevel.server)).size
      | none => if packModuleIsModule m then 3 else 1
    let some parts ← packModuleParts m false count.toUInt32 | fastImportFail s!"{i.module} cannot be served"
    return parts
  -- .ir.sig + .ir (optional)
  loadIR (i : Import) (m? : Option UInt32) : FastImportM (Array (ModuleData × CompactedRegion)) := do
    let some m := m? | do
      if let some parts := reused i true then return parts
      if let some arts := arts.find? i.module then
        noteRead (← readModuleDataParts arts.irParts)
      else
        readIR i.module
    unless ← packModuleServable m artsOf do fastImportFail s!"{i.module} is not read from its pack"
    match artsOf[m]? with
    | some arts =>
      if arts.irParts.isEmpty then return (← readModuleDataParts arts.irParts)
      let some parts ← packModuleParts m true arts.irParts.size.toUInt32 | fastImportFail s!"{i.module} cannot be served"
      return parts
    | none =>
      if let some parts ← packModuleParts m true 2 then return parts
      -- not packed: read as `importModulesCore` does
      readIR i.module

/--
The module data of the imports of `env`, an object that identifies them: it is created by the import
and kept by every environment derived from it (`setMainModule` replaces the header but not this
array) (`src/paperlean/interp_cache.cpp`, `src/paperlean/native_libs.cpp`).
-/
@[export lean_paperlean_env_imports_id]
private def envImportsId (env : Environment) : Array ModuleData := env.header.moduleData

/-- Whether `n` is an imported constant of `env` (`src/paperlean/interp_cache.cpp`). -/
@[export lean_paperlean_is_imported_const]
private def isImportedConst (env : Environment) (n : Name) : Bool := (env.getModuleIdxFor? n).isSome

/-- The artifacts given for packed modules, if they are the packed files; `none` if some are not. -/
private def packedArtifacts (arts : NameMap ImportArtifacts) (globalLevel : OLeanLevel) :
    Option (Std.HashMap UInt32 ImportArtifacts) := do
  let mut artsOf : Std.HashMap UInt32 ImportArtifacts := {}
  for (n, art) in arts do
    let m := packModuleFind n
    if m == noPackModule then continue
    let (oleans, irs) := packModulePaths m
    let given := art.oleanParts (inServer := globalLevel ≥ OLeanLevel.server)
    guard <| given.size ≤ oleans.size && (given.zip oleans).all fun (g, o) => g.toString == o
    guard <| art.irParts.size ≤ irs.size && (art.irParts.zip irs).all fun (g, o) => g.toString == o
    artsOf := artsOf.insert m art
  return artsOf

/-- The modules and their names in the order of `ImportState.moduleNames`. -/
private def FastImportState.result (s : FastImportState) : Array Name × Array ImportedModule :=
  let modules := s.order.map (s.records[·]!)
  (modules.map (·.module), modules)

@[export lean_paperlean_import_modules]
private def importModulesImpl (imports : Array Import) (levelIdx : UInt8) (arts : NameMap ImportArtifacts)
    (core : Unit → IO ImportState) : IO ImportState := do
  let level : OLeanLevel := match levelIdx with | 0 => .exported | 1 => .server | _ => .private
  importTimingMark "start"
  let mode ← importMode
  let isExported := level < .private
  -- The modules and the regions the traversal read from files.
  let fast (reuse : Option ImportState) :
      IO (Option ((Array Name × Array ImportedModule) × List CompactedRegion)) := do
    unless ← packsLoaded do return none
    let some artsOf := packedArtifacts arts level | return none
    let ref ← IO.mkRef ({} : FastImportState)
    match ← (fastImportModules imports level arts isExported artsOf reuse ref).toBaseIO with
    | .ok _ =>
      if ← importTimingEnabled then importTimingMark s!"modules.fast packed={(← ref.get).byPack.size}"
      return some ((← ref.get).result, (← ref.get).read)
    | .error e =>
      if ← importTimingEnabled then importTimingMark s!"modules.fallback ({e})"
      -- Release what was read from files before `importModulesCore` reads them again.
      for region in (← ref.get).read do
        unsafe region.free
      return none
  let s ← do
    if mode == 1 then
      core ()
    else if mode == 2 then
      let s ← core ()
      let legacyModules := s.moduleNames.filterMap (s.moduleNameMap[·]?)
      if let some ((moduleNames, modules), read) ← fast s then
        -- Only the modules are kept, not these arrays or the arrays of parts, so neither their
        -- identity nor their capacity matters.
        if let some d := unsafe PaperLean.graphDiff (s.moduleNames.toList, legacyModules.toList)
            (moduleNames.toList, modules.toList) false then
          throw <| IO.userError s!"PAPERLEAN_IMPORT=check: the imported modules differ from the legacy import: {d}"
        -- the legacy import's regions are kept
        for region in read do
          unsafe region.free
      pure s
    else if let some ((moduleNames, modules), _) ← fast none then
      pure { moduleNames, moduleNameMap := modules.foldl (fun m mod => m.insert mod.module mod) {} }
    else
      core ()
  importTimingMark "modules"
  return s

end Lean
