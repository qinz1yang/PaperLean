/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Init.System.IO

-- (no `SizeOf` instances for PaperLean's types: an instance of a module of `Lean` would be one of
-- every environment that imports it, which Lean's searches would try)
set_option genSizeOf false
set_option genInjectivity false

public section

/-!
The switches of PaperLean's faster import (`Lean.PaperLean.Import`): `PAPERLEAN_IMPORT=legacy` runs
only Lean's code, `PAPERLEAN_IMPORT=check` runs both and fails the import if their results differ in
any object, and `PAPERLEAN_IMPORT_TIMING` reports the cost of each import step on stderr.
`PAPERLEAN_EXACT` turns off reusing results, not olean packs, import images or the faster import: a
difference of these from Lean's import does not show when comparing with it, only with `check`.
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
identity and ignores the state, and whose `addEntry` is the one that the replay models: the instance
extension and the simp sets in `simpExtensionMapRef`, which `mkSimpExt` made.
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

/-- `f a b c`, after which the thread's heartbeat counter is as before: for PaperLean's work in pure
code, which counts no heartbeats. Only where `nativeAvailable` (`f` should be a constant, which
the call does not allocate). -/
@[extern "lean_paperlean_uncounted"]
def uncounted {α β γ δ : Type} (f : α → β → γ → δ) (a : α) (b : β) (c : γ) : δ := f a b c

/-- `uncounted` with five borrowed arguments: for the records of `envRecord`, built counting no
heartbeats, with the calling conventions of the hooks' callers kept. -/
@[extern "lean_paperlean_uncounted5"]
def uncounted5 {α β γ δ ε ζ : Type} (f : @& (α → β → γ → δ → ε → ζ)) (a : @& α) (b : @& β)
    (c : @& γ) (d : @& δ) (e : @& ε) : ζ := f a b c d e

/-- `IO.setNumHeartbeats count`, for PaperLean's own work, which counts no heartbeats. Only where
`nativeAvailable`. -/
@[extern "lean_paperlean_set_heartbeats"]
opaque setHeartbeats (count : @& Nat) : BaseIO Unit

/-- `core ()`, the import state of `importModulesCore` at `OLeanLevel` `level` (its constructor
index), computed faster from olean packs if possible. -/
@[extern "lean_paperlean_import_modules"]
opaque importModulesHook {ι ρ σ : Type} (imports : ι) (level : UInt8) (arts : ρ) (core : Unit → IO σ) :
    IO σ

/-!
Recording of environment accesses (`Lean.PaperLean.EnvDeps`, `src/paperlean/env_recorder.cpp`).
While a thread records, the functions through which the environment is read pass each access to the
recorder, with a check of whether another environment gives the same answer; and accesses that
cannot be checked make the recording unusable.
-/

/-- An access to the environment, as recorded. Open declarations are a `List OpenDecl`, as an object:
this module lies below `Lean.Data.OpenDecl`, which `Lean.Environment` does not import. -/
inductive EnvAccess where
  /-- The state of extension `idx`, with async mode `mode` (`EnvAccess.asyncModeIdx`) for `decl`. -/
  | ext (idx : Nat) (mode : Nat) (decl : Name)
  /-- The part `part` of the state of extension `idx`, e.g. the instances of one class. -/
  | extPart (idx : Nat) (part : Name)
  /-- A lookup of constant `n` (`Environment.findAsync?` and the functions built on it). -/
  | const (n : Name) (skipRealize : Bool)
  /-- The resolution of identifier `id` in namespace `ns` with the open declarations `openDecls`
  (`ResolveName.resolveGlobalName`). -/
  | resolve (id : Name) (ns : Name) (openDecls : NonScalar)
  /-- The resolution of namespace `id` in namespace `ns` with the open declarations `openDecls`
  (`ResolveName.resolveNamespace`). -/
  | resolveNamespace (id : Name) (ns : Name) (openDecls : NonScalar)
  /-- An operation on one of Lean's caches of `MetaM` (numbered as in `Lean.PaperLean.TCCache`): a
  lookup of `key` that found `value`, an `Option` (`op = 0`), or the insertion of `value` under
  `key` (`op = 1`) (`noteCache`). -/
  | cache (cache op : UInt8) (key value : NonScalar)
  /-- A read of the current namespace and open declarations of the recording by `decl`, otherwise
  than to resolve a name. -/
  | scope (decl : Name)
  /-- A read of whether realizations are enabled for the constant `c`, which is not imported
  (`Environment.areRealizationsEnabledForConst`). -/
  | realizations (c : Name)

/-- Whether this thread records environment accesses (`dummy` keeps the call from being shared). -/
@[extern "lean_paperlean_env_recording"]
opaque envRecording {α : Type} (dummy : @& α) : Bool

/-- `r`, after recording `access` with `check` (a function of an environment, the current namespace
and the open declarations to `Bool`), if this thread records. -/
@[extern "lean_paperlean_env_record"]
def envRecord {α : Type} (_access : EnvAccess) (_check : NonScalar) (r : α) : α := r

/-- `r`, after making this thread's recording unusable because of `why`, if it records: for reads
that cannot be checked, such as of the whole constant map or of the kernel environment. -/
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

/-!
Hooks in front of an upstream function's body, whose compiled code must stay official Lean's: code
built by official Lean that inlined the function, or reuses its specializations, calls what that
code generates (`_spec_`, `_lam_`, `_redArg`, `unsafe_`), with official Lean's signatures. `if` does
not keep them: in its `false` branch the compiler replaces the constructors `false` of the body by
the condition, which closures of the body then capture. So these hooks branch on a type of their
own, whose constructors no upstream body has.
-/

/-- Which code a hook in front of an upstream function's body runs. -/
inductive HookPath where
  | upstream | hook

/-- `hook`, where `nativeAvailable`, else `upstream`, which is an upstream function's body. -/
@[extern "lean_paperlean_native_available"]
opaque nativePath {α : Type} (dummy : @& α) : HookPath := .upstream

/-- `hook`, while this thread records environment accesses, else `upstream`. -/
@[extern "lean_paperlean_env_recording"]
opaque recordingPath {α : Type} (dummy : @& α) : HookPath := .upstream

/-- `hook` on `HookPath.hook`, else `upstream`. -/
@[macro_inline, expose] def HookPath.select {β : Sort _} (p : HookPath) (hook upstream : β) : β :=
  HookPath.casesOn p upstream hook

/-- Whether `n` lies in the namespaces of PaperLean's own code, `Lean.PaperLean` and `Lake.PaperLean`,
however it is prefixed. -/
private def isOwnName : Name → Bool
  | .str p s => (s == "PaperLean" && match p with
      | .str _ r => r == "Lean" || r == "Lake"
      | _ => false) || isOwnName p
  | .num p _ => isOwnName p
  | .anonymous => false

/-- `hook` if `n`, a specialization, was made for PaperLean's own code, which official Lean does not
have, else `upstream`. -/
@[noinline] def ownSpecPath (n : @& Name) : HookPath :=
  if isOwnName n then .hook else .upstream

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

/-- Makes this thread's recording unusable, if it records, because it runs a tactic. (Not after a test of
`envRecording ()`: of a constant, the compiler keeps the first result.) -/
@[noinline] def noteTactic : BaseIO Unit :=
  envMarkUnusableIO "a tactic"

/-- Records the accesses `accesses` with their checks `checks` (of an earlier recording, e.g. of a
result reused within this computation), if this thread records. -/
@[extern "lean_paperlean_env_record_all"]
opaque envRecordAll (accesses : @& Array EnvAccess) (checks : @& Array NonScalar) : BaseIO Unit

/-- Starts recording this thread's accesses to the environment. -/
@[extern "lean_paperlean_env_start_recording"]
opaque envStartRecording : BaseIO Unit

/-- Ends the recording that this thread started last: the accesses, their checks, and why it is
unusable (its reasons, separated by `; `; empty if it is usable). -/
@[extern "lean_paperlean_env_stop_recording"]
opaque envStopRecording : BaseIO (Array EnvAccess × Array NonScalar × String)

/-- `Option` as it is at run time, for objects that `foundCopy` makes (it would keep those of an
`Option`). -/
private inductive Found where
  | none
  | some (value : NonScalar)

/-- A copy of the result of a lookup, an `Option`, in an object of its own. If a record held Lean's,
Lean could not reuse that object for its own result, as it does otherwise, and would count another. -/
private unsafe def foundCopy (found? : NonScalar) : NonScalar :=
  match (unsafeCast found? : Option NonScalar) with
  | .some value => unsafeCast (Found.some value)
  | .none => unsafeCast Found.none

/-- Records the operation `op` (as in `EnvAccess.cache`) of the computation on the cache `cache`
with `key` and `value`, if this thread records, counting no heartbeats. Called by Lean's functions
that use the caches, only while the thread records (`envRecording`). -/
@[noinline] def noteCache {κ ν : Type} (cache op : UInt8) (key : κ) (value : ν) : BaseIO Unit := do
  let heartbeats ← IO.getNumHeartbeats
  let value : NonScalar := unsafe if op == 0 then foundCopy (unsafeCast value) else unsafeCast value
  -- (a cache operation has no check of its own: `Lean.PaperLean.TCCache` checks them in order)
  envRecordAll #[.cache cache op (unsafe unsafeCast key) value] #[unsafe unsafeCast ()]
  setHeartbeats heartbeats

end Lean.PaperLean
