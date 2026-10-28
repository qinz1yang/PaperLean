/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.Environment
public import Lean.Data.OpenDecl
import all Lean.Environment
import all Lean.ExtraModUses
import Std.Data.HashSet

public section

/-!
The dependencies of a computation on the environment, recorded so that its result can be reused in
another environment where every access gives the same answer (`Lean.PaperLean.SectionVars`).

While a thread records (`Lean.PaperLean.Base`, `src/paperlean/env_recorder.cpp`), each read of the
environment through `Lean.Environment`'s functions is recorded with a check:
* each extension state read (`EnvExtension.getState`) must be the same object;
* each lookup of a constant that is not imported (`Environment.findAsync?` and the functions built
  on it) must find a constant, or not, as before (imported constants of a visibility do not change);
* each resolution of a global name or namespace (`ResolveName.resolveGlobalName`,
  `ResolveName.resolveNamespace`) must give the same answer with the namespace and the open
  declarations of the reuse (the accesses made for it are not recorded).

Reads that cannot be checked make the recording unusable: of the kernel environment, of all of the
module's constants, through `Environment.findTask`; so do tactics, tasks that the thread starts,
and, with `PAPERLEAN_REUSE_USER_ELABS=0`, term elaborators that are not Lean's own. The
computation may change the environment only by records of module uses (`Lean.ExtraModUses`): the
entries it adds are repeated on reuse where they are missing, as Lean adds them, and the reads of
these extensions, which only decide whether to add an entry, are not recorded.
-/

namespace Lean.PaperLean.EnvDeps

/-- The recorded dependencies of a computation. -/
structure Deps where
  /-- Checks of an environment, current namespace and open declarations. -/
  checks : Array (Environment → Name → List OpenDecl → Bool)
  /-- The changes to the environment, as functions that repeat them. -/
  replays : Array (Environment → Environment)
  /-- The access of each check. -/
  accesses : Array EnvAccess
deriving Inhabited

/-- Whether the dependencies hold in `env` with namespace `ns` and open declarations `openDecls`. -/
def Deps.hold (d : Deps) (env : Environment) (ns : Name) (openDecls : List OpenDecl) : Bool :=
  d.checks.all (· env ns openDecls)

/-- The access of the first check that does not hold, if any. -/
def Deps.firstFailure? (d : Deps) (env : Environment) (ns : Name) (openDecls : List OpenDecl) :
    Option EnvAccess := Id.run do
  for c in d.checks, a in d.accesses do
    unless c env ns openDecls do
      return some a
  return none

/-- A description of an access, for debugging. -/
def describe (env : Environment) : EnvAccess → String
  | .ext idx mode decl =>
    let exts := unsafe unsafeBaseIO persistentEnvExtensionsRef.get
    let name := exts.find? (·.toEnvExtension.idx == idx) |>.map (·.name.toString) |>.getD s!"#{idx}"
    let _ := env
    s!"extension {name} (mode {mode}{if decl.isAnonymous then "" else s!", {decl}"})"
  | .const n _ => s!"constant {n}"
  | .resolve id => s!"name {id}"
  | .resolveNamespace id => s!"namespace {id}"
  | .modify idx => s!"change of extension #{idx}"
  | .replay idx => s!"replayed change of extension #{idx}"

/-- `env` with the computation's changes repeated. -/
def Deps.replay (d : Deps) (env : Environment) : Environment :=
  d.replays.foldl (fun env f => f env) env

private def accessKey : EnvAccess → Option (Nat × Nat × Name × Bool)
  | .ext idx mode decl => some (0, idx, decl, mode == 0)
  | .const n skipRealize => some (1, 0, n, skipRealize)
  | .resolve id => some (2, 0, id, false)
  | .resolveNamespace id => some (3, 0, id, false)
  | .modify _ | .replay _ => none

private def extModeKey : EnvAccess → Nat
  | .ext _ mode _ => mode
  | _ => 0

/-- The extensions of module uses (`Lean.ExtraModUses`), whose changes are repeated on reuse
(`moduleUseReplays`) and whose reads are not recorded. Apart from the entries of the module, which
decide only whether an entry is added again, their states hold only imported data. -/
private def moduleUseExts : Array Nat :=
  #[extraModUses.toEnvExtension.idx, indirectModUseExt.toEnvExtension.idx]

/-- The elements of `new` before its suffix `old` (the same list cells), the oldest first. -/
private unsafe def addedEntriesImpl {α : Type} (old new : List α) : List α :=
  go new []
where
  go : List α → List α → List α
    | l, acc => if ptrAddrUnsafe l == ptrAddrUnsafe old then acc else
      match l with
      | [] => acc
      | x :: xs => go xs (x :: acc)

@[implemented_by addedEntriesImpl]
private opaque addedEntries {α : Type} (old new : List α) : List α

/-- The entries that a computation added to the extensions of module uses between `before` and
`after`, as functions that add them where they are missing, as `recordExtraModUseCore` and
`recordIndirectModUse` do. -/
private def moduleUseReplays (before after : Environment) : Array (Environment → Environment) :=
  let extra := addedEntries (extraModUses.getEntries (asyncMode := .local) before)
    (extraModUses.getEntries (asyncMode := .local) after)
  let indirect := addedEntries (indirectModUseExt.getEntries (asyncMode := .mainOnly) before)
    (indirectModUseExt.getEntries (asyncMode := .mainOnly) after)
  (extra.map fun e env =>
    if (extraModUses.getState (asyncMode := .local) env).contains e then env
    else extraModUses.addEntry env e).toArray ++
  (indirect.map fun e env =>
    if (indirectModUseExt.getEntries (asyncMode := .mainOnly) env).contains e then env
    else indirectModUseExt.addEntry env e).toArray

/-- Whether `a` and `b` are equal but in the states of the extensions `allowed`. -/
private unsafe def sameButImpl (a b : Environment) (allowed : Array Nat) : Bool :=
  ptrEq a.asyncConstsMap b.asyncConstsMap && ptrEq a.asyncCtx? b.asyncCtx? &&
    ptrEq a.importRealizationCtx? b.importRealizationCtx? &&
    ptrEq a.localRealizationCtxMap b.localRealizationCtxMap &&
    ptrEq a.allRealizations b.allRealizations &&
    a.isExporting == b.isExporting && ptrEq a.serverBaseExts b.serverBaseExts &&
    sameKernel a.base.private b.base.private && sameKernel a.base.public b.base.public
where
  sameKernel (x y : Kernel.Environment) : Bool :=
    ptrEq x.constants y.constants && x.quotInit == y.quotInit &&
      ptrEq x.diagnostics y.diagnostics && ptrEq x.const2ModIdx y.const2ModIdx &&
      ptrEq x.irBaseExts y.irBaseExts && ptrEq x.header y.header &&
      x.extensions.size == y.extensions.size &&
      (List.range x.extensions.size).all fun i =>
        allowed.contains i || ptrEq x.extensions[i]! y.extensions[i]!

@[implemented_by sameButImpl]
private opaque sameBut (a b : Environment) (allowed : Array Nat) : Bool

private unsafe def toDepsImpl (accesses : Array EnvAccess) (checks : Array NonScalar) :
    Deps := Id.run do
  let mut seen : Std.HashSet (Nat × Nat × Name × Bool × Nat) := {}
  let mut cs : Array (Environment → Name → List OpenDecl → Bool) := #[]
  let mut as : Array EnvAccess := #[]
  let mut rs : Array (Environment → Environment) := #[]
  for a in accesses, c in checks do
    match a with
    | .replay _ => rs := rs.push (unsafeCast c)
    | .modify _ => pure ()
    | _ =>
      if let .ext idx .. := a then
        if moduleUseExts.contains idx then continue
      let some (k, i, n, b) := accessKey a | continue
      let key := (k, i, n, b, extModeKey a)
      unless seen.contains key do
        seen := seen.insert key
        cs := cs.push (unsafeCast c)
        as := as.push a
  return { checks := cs, replays := rs, accesses := as }

@[implemented_by toDepsImpl]
private opaque toDeps (accesses : Array EnvAccess) (checks : Array NonScalar) : Deps

/-- A recording in progress on this thread. -/
structure Recording where
  private before : Environment
  /-- The result once stopped. -/
  private result : IO.Ref (Option (Except String Deps))

/-- Starts recording this thread's accesses to the environment. -/
def start [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] : m Recording := do
  let before ← getEnv
  let result ← (IO.mkRef none : BaseIO _)
  (envStartRecording : BaseIO Unit)
  return { before, result }

/--
Ends the recording `r` (if it has not ended yet; it must be the one this thread started last): the
dependencies if the recording is usable and the environment, which is now `getEnv`, has changed only
by changes recorded as replayable, else why not.
-/
def Recording.stop [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] (r : Recording) :
    m (Except String Deps) := do
  if let some d ← (r.result.get : BaseIO _) then
    return d
  let (accesses, checks, why) ← (envStopRecording : BaseIO _)
  let after ← getEnv
  let allowed := moduleUseExts ++ accesses.filterMap fun | .replay idx => some idx | _ => none
  let d := if !why.isEmpty then .error why
    else if unsafe ptrEq r.before after then .ok (toDeps accesses checks)
    else if sameBut r.before after allowed then
      let deps := toDeps accesses checks
      .ok { deps with replays := deps.replays ++ moduleUseReplays r.before after }
    else .error "a change of the environment"
  (r.result.set (some d) : BaseIO Unit)
  return d

end Lean.PaperLean.EnvDeps
