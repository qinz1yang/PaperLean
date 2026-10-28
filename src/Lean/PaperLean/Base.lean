/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Init.System.IO

public section

/-!
The switches of PaperLean's faster import (`Lean.PaperLean.Import`): `PAPERLEAN_IMPORT=legacy` runs
only Lean's code, `PAPERLEAN_IMPORT=check` runs both and fails the import if their results differ in
any object, and `PAPERLEAN_IMPORT_TIMING` reports the cost of each import step on stderr.
-/

namespace Lean.PaperLean

/-- `0`: the faster implementations, `1`: `legacy`, `2`: `check`. -/
@[extern "lean_paperlean_import_mode"]
opaque importMode : BaseIO UInt8

@[extern "lean_paperlean_import_timing_enabled"]
opaque importTimingEnabled : BaseIO Bool

/-- Reports the cost of the import step that just ended if `PAPERLEAN_IMPORT_TIMING` is set. -/
@[extern "lean_paperlean_import_timing_mark"]
opaque importTimingMark (step : @& String) : BaseIO Unit

/--
The state that `ScopedEnvExtension.addImportedFn` folds from the global entries of `as` (those of
each imported module) of the extension named `extName`, starting from `initial`, if it is built
faster (`Lean.PaperLean.ImportState`), which happens only for extensions whose `ofOLeanEntry` is the
identity and ignores the state.
-/
@[extern "lean_paperlean_imported_state"]
opaque importedState? {β σ : Type} (extName : @& Name) (initial : @& σ) (as : @& Array (Array β)) :
    BaseIO (Option σ)

@[extern "lean_paperlean_check_imported_state"]
private opaque checkImportedState {σ : Type} (extName : Name) (fast fold : σ) : IO Unit

/-- `fast`, after `PAPERLEAN_IMPORT=check` has compared it with `fold` if `check` (failing if they
differ). -/
def checkedImportedState {σ : Type} (extName : Name) (fast fold : σ) (check : Bool) : IO σ := do
  if check then checkImportedState extName fast fold
  return fast

/-!
Hooks of PaperLean's faster import in `Lean.Environment`, implemented in `Lean.PaperLean.Import` and
`src/paperlean`. They are declared here, with the types of `Lean.Environment` as type parameters
(objects, as at run time; scalars keep their types), so that `Lean.Environment` keeps upstream's
lines: its hooks are calls on lines of its own.
-/

/-- The entries of an imported module for an extension it has none for, in `setImportedEntries` and
in its faster version: one object for all. -/
def noImportedEntries {α : Type} : Array α := #[]

/-- `core ()`, `setImportedEntries states mods startingAt`, built faster if possible; `persistent`
allows allocating persistent objects. -/
@[extern "lean_paperlean_set_imported_entries"]
opaque setImportedEntriesHook {σ μ : Type} (states : σ) (mods : μ) (startingAt : Nat) (persistent : Bool)
    (core : Unit → IO σ) : IO σ

/-- Starts building the imported states of the persistent extensions from the `startingAt`-th on in
the background where possible, from their `importedEntries` in `env`. -/
@[extern "lean_paperlean_prefetch_imported_states"]
opaque prefetchImportedStates {ε ω : Type} (env : ε) (opts : ω) (startingAt : Nat) (persistent : Bool) :
    BaseIO Unit

/-- Waits for the states built in the background for `env` that were not used and releases them. -/
@[extern "lean_paperlean_drop_prefetched_states"]
opaque dropPrefetchedStates {ε : Type} (env : ε) : BaseIO Unit

/-- `fold ()`, the imported state of the extension `extName` for its entries `as`: the one built in
the background if it was, otherwise `fold ()` run with the interpreter's symbol cache shared across
the import. -/
@[extern "lean_paperlean_imported_extension_state"]
opaque importedExtensionState {α ε ω σ : Type} (extName : Name) (as : α) (env : ε) (opts : ω)
    (fold : Unit → IO σ) : IO σ

/-- `d.isModule`, read from the olean pack's tables if `d` is packed. -/
@[extern "lean_paperlean_module_data_is_module"]
opaque moduleDataIsModule {μ : Type} (d : @& μ) : Bool

/-- `d.constants.size`, as `moduleDataIsModule`. -/
@[extern "lean_paperlean_module_data_num_constants"]
opaque moduleDataNumConstants {μ : Type} (d : @& μ) : Nat

/-- `d.extraConstNames.size`, as `moduleDataIsModule`. -/
@[extern "lean_paperlean_module_data_num_extra_const_names"]
opaque moduleDataNumExtraConstNames {μ : Type} (d : @& μ) : Nat

/-- The private constant map and `const2ModIdx` of `finalizeImport` built faster, with the module
index and name for which its fold calls `throwAlreadyImported`, if any; `none`: built by the fold. -/
@[extern "lean_paperlean_private_constant_maps"]
opaque privateConstantMaps? {μ ρ : Type} (moduleData irData : μ) (privateCapacity c2mCapacity : Nat)
    (persistent : Bool) : IO (Option ρ)

/-- `PAPERLEAN_IMPORT=check`: fails if the private maps built faster differ from the fold's. -/
@[extern "lean_paperlean_check_private_constant_maps"]
opaque checkPrivateConstantMaps {ρ π κ : Type} (fast : ρ) (privateConstantMap : π) (const2ModIdx : κ) :
    IO Unit

/-- The public constant map of `finalizeImport` built faster; `none`: built by the fold. -/
@[extern "lean_paperlean_public_constant_map"]
opaque publicConstantMap? {ι π : Type} (modules : ι) (capacity : Nat) (isModule persistent : Bool) :
    IO (Option π)

/-- `PAPERLEAN_IMPORT=check`: fails if the public map built faster differs from the fold's. -/
@[extern "lean_paperlean_check_public_constant_map"]
opaque checkPublicConstantMap {π : Type} (fast fold : π) : IO Unit

/-- Runs `act`, after which the thread's heartbeat counter is as before: an import counts no
heartbeats, so PaperLean, whose import differs from Lean's, never counts more. -/
@[extern "lean_paperlean_uncounted_heartbeats"]
opaque uncountedHeartbeats {α : Type} (act : IO α) : IO α

/-- `core ()`, the import state of `importModulesCore` at `OLeanLevel` `level` (its constructor
index), computed faster from olean packs if possible. -/
@[extern "lean_paperlean_import_modules"]
opaque importModulesHook {ι ρ σ : Type} (imports : ι) (level : UInt8) (arts : ρ) (core : Unit → IO σ) :
    IO σ

/-!
Recording of environment accesses (`Lean.PaperLean.EnvDeps`, `src/paperlean/env_recorder.cpp`).
While a thread records, the functions through which the environment is read pass each access to the
recorder, with a check of whether another environment (with the current namespace and open
declarations) gives the same answer; changes to the environment are passed too, those that can be
repeated with a function that repeats them; and accesses that cannot be checked make the recording
unusable.
-/

/-- An access to the environment, as recorded. -/
inductive EnvAccess where
  /-- The state of extension `idx`, with async mode `mode` (`EnvAccess.asyncModeIdx`) for `decl`. -/
  | ext (idx : Nat) (mode : Nat) (decl : Name)
  /-- A lookup of constant `n` (`Environment.findAsync?` and the functions built on it). -/
  | const (n : Name) (skipRealize : Bool)
  /-- The resolution of identifier `id` (`ResolveName.resolveGlobalName`). -/
  | resolve (id : Name)
  /-- The resolution of namespace `id` (`ResolveName.resolveNamespace`). -/
  | resolveNamespace (id : Name)
  /-- A change to the state of extension `idx`. -/
  | modify (idx : Nat)
  /-- A change to the state of extension `idx` that the check, a function on environments,
  repeats. -/
  | replay (idx : Nat)

/-- Whether this thread records environment accesses (`dummy` keeps the call from being shared). -/
@[extern "lean_paperlean_env_recording"]
opaque envRecording {α : Type} (dummy : @& α) : Bool

/-- `r`, after recording `access` with `check` (a function of an environment, the current namespace
and the open declarations to `Bool`, or for `EnvAccess.replay`, of an environment to an
environment), if this thread records. -/
@[extern "lean_paperlean_env_record"]
def envRecord {α : Type} (_access : EnvAccess) (_check : NonScalar) (r : α) : α := r

/-- `r`, after making this thread's recording unusable because of `why` (a literal), if it records:
for reads that cannot be checked, such as of the whole constant map or of the kernel environment. -/
@[extern "lean_paperlean_env_mark_unusable"]
def envMarkUnusable {α : Type} (_why : @& String) (r : α) : α := r

/-- `f ()`, with this thread's recording, if any, paused: for functions whose result is recorded as
a whole. -/
@[extern "lean_paperlean_env_without_recording"]
def envWithoutRecording {α : Type} (f : Unit → α) : α := f ()

/-- Whether PaperLean's native code is available: `false` only in the stage0 `lean` that builds
stage1, when it interprets stage1's code (`src/paperlean/stage0_shim.c`). -/
@[extern "lean_paperlean_native_available"]
opaque nativeAvailable {α : Type} (dummy : @& α) : Bool

/-- Pauses this thread's recording, if it records, until `envResume`; returns whether it did. For
computations whose result does not depend on the environment that the recording is about. -/
@[extern "lean_paperlean_env_pause"]
opaque envPause : BaseIO Bool

/-- Ends a pause of `envPause`, given its result. -/
@[extern "lean_paperlean_env_resume"]
opaque envResume (paused : Bool) : BaseIO Unit

/-- Makes this thread's recording unusable because of `why`, if it records. -/
@[extern "lean_paperlean_env_mark_unusable_io"]
opaque envMarkUnusableIO (why : @& String) : BaseIO Unit

/-- Records the accesses `accesses` with their checks `checks` (of an earlier recording, e.g. of a
result reused within this computation), if this thread records. -/
@[extern "lean_paperlean_env_record_all"]
opaque envRecordAll (accesses : @& Array EnvAccess) (checks : @& Array NonScalar) : BaseIO Unit

@[extern "lean_paperlean_env_start_recording"]
opaque envStartRecording : BaseIO Unit

/-- Ends the recording that this thread started last: the accesses, their checks, and why it is
unusable (empty if it is usable). -/
@[extern "lean_paperlean_env_stop_recording"]
opaque envStopRecording : BaseIO (Array EnvAccess × Array NonScalar × String)

end Lean.PaperLean
