/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Attributes import Lean.PaperLean.Base

public section

namespace Lean

namespace ScopedEnvExtension

inductive Entry (α : Type) where
  | global : α → Entry α
  | scoped : Name → α → Entry α

structure State (σ : Type) where
  state        : σ
  activeScopes : NameSet := {}
  delimitsLocal : Bool := true -- used for implementing `end_local_scope`.

structure ScopedEntries (β : Type) where
  map : SMap Name (PArray β) := {}
  deriving Inhabited
structure StateStack (α : Type) (β : Type) (σ : Type) where
  stateStack    : List (State σ) := {}
  scopedEntries : ScopedEntries β := {}
  newEntries    : List (Entry α) := []
  deriving Inhabited

structure Descr (α : Type) (β : Type) (σ : Type) where
  name           : Name := by exact decl_name%
  mkInitial      : IO σ
  ofOLeanEntry   : σ → α → ImportM β
  toOLeanEntry   : β → α
  addEntry       : σ → β → σ
  finalizeImport : σ → σ := id
  exportEntry?   : Environment → α → OLeanEntries (Option α) := fun _ a => .uniform (some a)

instance [Inhabited α] : Inhabited (Descr α β σ) where
  default := {
    name         := default
    mkInitial    := default
    ofOLeanEntry := default
    toOLeanEntry := default
    addEntry     := fun s _ => s
  }

def mkInitial (descr : Descr α β σ) : IO (StateStack α β σ) :=
  return { stateStack := [ { state := (← descr.mkInitial ) } ] }

def ScopedEntries.insert (scopedEntries : ScopedEntries β) (ns : Name) (b : β) : ScopedEntries β :=
  match scopedEntries.map.find? ns with
  | none    => { map := scopedEntries.map.insert ns <| ({} : PArray β).push b }
  | some bs => { map := scopedEntries.map.insert ns <| bs.push b }

/-- Fold imports in declaration order. Only global insertion varies for the builtin parser;
the initial state, scoped entry conversion and finalization always use the descriptor. -/
@[inline] def foldImported (descr : Descr α β σ) (as : Array (Array (Entry α))) (initial : δ)
    (addGlobal : σ → δ → α → ImportM (σ × δ)) : ImportM (StateStack α β σ) := do
  let mut s ← descr.mkInitial
  let mut extra := initial
  let mut scopedEntries : ScopedEntries β := {}
  for a in as do
    for e in a do
      match e with
      | Entry.global a =>
        let (next, extra') ← addGlobal s extra a
        s := next
        extra := extra'
      | Entry.scoped ns a =>
        let b ← descr.ofOLeanEntry s a
        scopedEntries := scopedEntries.insert ns b
  s := descr.finalizeImport s
  return { stateStack := [ { state := s } ], scopedEntries := scopedEntries }

def addImportedFn (descr : Descr α β σ) (as : Array (Array (Entry α))) : ImportM (StateStack α β σ) :=
  foldImported descr as () fun s _ a => do
    return (descr.addEntry s (← descr.ofOLeanEntry s a), ())

/-- PaperLean: `addImportedFn`, with the state of the global entries built faster, which is the
function that extensions run on import. -/
@[noinline] def _root_.Lean.PaperLean.addImportedFnFast (descr : Descr α β σ) (as : Array (Array (Entry α))) : ImportM (StateStack α β σ) := do
  let mut s ← descr.mkInitial; let fast? ← PaperLean.importedState? descr.name s as -- PaperLean: faster
  let mut scopedEntries : ScopedEntries β := {}; let fold := fast?.isNone || (← PaperLean.importMode) == 2
  for a in as do
    for e in a do
      match e with
      | Entry.global a =>
        if fold then
          let b ← descr.ofOLeanEntry s a; s := descr.addEntry s b
      | Entry.scoped ns a =>
        let b ← descr.ofOLeanEntry s a
        scopedEntries := scopedEntries.insert ns b
  s := descr.finalizeImport s; if let some fast := fast? then s ← PaperLean.checkedImportedState descr.name (descr.finalizeImport fast) s fold
  return { stateStack := [ { state := s } ], scopedEntries := scopedEntries }

def addEntryFn (descr : Descr α β σ) (s : StateStack α β σ) (e : Entry β) : StateStack α β σ :=
  match s with
  | { stateStack := stateStack, scopedEntries := scopedEntries, newEntries := newEntries } =>
    match e with
    | Entry.global b => {
        scopedEntries := scopedEntries
        newEntries    := (Entry.global (descr.toOLeanEntry b)) :: newEntries
        stateStack    := stateStack.map fun s => { s with state := descr.addEntry s.state b }
      }
    | Entry.«scoped» ns b =>
      {
        scopedEntries := scopedEntries.insert ns b
        newEntries    := (Entry.«scoped» ns (descr.toOLeanEntry b)) :: newEntries
        stateStack    := stateStack.map fun s =>
          if s.activeScopes.contains ns then
            { s with state := descr.addEntry s.state b }
          else
            s
      }

def exportEntriesFn (descr : Descr α β σ) (env : Environment) (s : StateStack α β σ) : OLeanEntries (Array (Entry α)) := Id.run do
  let mut exported : Array (Entry α) := #[]
  let mut server   : Array (Entry α) := #[]
  let mut priv     : Array (Entry α) := #[]
  for entry in s.newEntries.toArray.reverse do
    match entry with
    | .global e =>
      let r := descr.exportEntry? env e
      if let some e := r.exported then exported := exported.push (.global e)
      if let some e := r.server   then server   := server.push   (.global e)
      if let some e := r.private  then priv     := priv.push     (.global e)
    | .scoped ns e =>
      let r := descr.exportEntry? env e
      if let some e := r.exported then exported := exported.push (.scoped ns e)
      if let some e := r.server   then server   := server.push   (.scoped ns e)
      if let some e := r.private  then priv     := priv.push     (.scoped ns e)
  return { exported, server, «private» := priv }

end ScopedEnvExtension

open ScopedEnvExtension

structure ScopedEnvExtension (α : Type) (β : Type) (σ : Type) where
  descr : Descr α β σ
  ext   : PersistentEnvExtension (Entry α) (Entry β) (StateStack α β σ)
  deriving Inhabited

builtin_initialize scopedEnvExtensionsRef : IO.Ref (Array (ScopedEnvExtension EnvExtensionEntry EnvExtensionEntry EnvExtensionState)) ← IO.mkRef #[]

/-- Register a scoped extension with its import fold. The remaining registration fields are
shared by the standard scoped extension and the builtin parser. -/
@[macro_inline, expose] unsafe def _root_.Lean.PaperLean.registerScopedEnvExtensionWithImport
    (descr : Descr α β σ) (addImported : Array (Array (Entry α)) → ImportM (StateStack α β σ)) :
    IO (ScopedEnvExtension α β σ) := do
  let ext ← registerPersistentEnvExtension {
    name            := descr.name
    mkInitial       := mkInitial descr
    addImportedFn   := addImported
    addEntryFn      := addEntryFn descr
    exportEntriesFnEx := exportEntriesFn descr
    statsFn         := fun s => format "number of local entries: " ++ format s.newEntries.length
    -- We restrict addition of global and `scoped` entries to the main thread but allow addition of
    -- scopes and local entries in any thread, which are visible only in that thread (see uses of
    -- `AsyncMode.local` below). Allowing the latter is important for tactics such as -- `classical`
    -- or `open in`.
    asyncMode       := .mainOnly
  }
  let ext := { descr := descr, ext := ext : ScopedEnvExtension α β σ }
  scopedEnvExtensionsRef.modify fun exts => exts.push (unsafeCast ext)
  return ext

-- PaperLean: (not inlined: its body calls PaperLean's code)
@[noinline] unsafe def registerScopedEnvExtensionUnsafe (descr : Descr α β σ) : IO (ScopedEnvExtension α β σ) :=
  PaperLean.registerScopedEnvExtensionWithImport descr (PaperLean.addImportedFnFast descr)

@[implemented_by registerScopedEnvExtensionUnsafe]
opaque registerScopedEnvExtension (descr : Descr α β σ) : IO (ScopedEnvExtension α β σ)

def ScopedEnvExtension.pushScope (ext : ScopedEnvExtension α β σ) (env : Environment) : Environment :=
  ext.ext.modifyState (asyncMode := .local) env fun s =>
    match s.stateStack with
    | [] => s
    | state :: stack => { s with stateStack := { state with delimitsLocal := true } :: state :: stack }

def ScopedEnvExtension.popScope (ext : ScopedEnvExtension α β σ) (env : Environment) : Environment :=
  ext.ext.modifyState (asyncMode := .local) env fun s =>
    match s.stateStack with
    | _      :: state₂ :: stack => { s with stateStack := state₂ :: stack }
    | _ => s

/-- Modifies `delimitsLocal` flag to `false` on the top `depth` entries of the state stack,
to turn off delimiting of local entries across multiple implicit scope levels
(e.g. those introduced by compound `namespace A.B.C` expansions).
-/
def ScopedEnvExtension.setDelimitsLocal (ext : ScopedEnvExtension α β σ) (env : Environment) (depth : Nat) : Environment :=
  ext.ext.modifyState (asyncMode := .local) env fun s =>
    {s with stateStack := go depth s.stateStack}
where
  go : Nat → List (State σ) → List (State σ)
    | 0, stack => stack
    | _, [] => []
    | n + 1, state :: stack => {state with delimitsLocal := false} :: go n stack

def ScopedEnvExtension.addEntry (ext : ScopedEnvExtension α β σ) (env : Environment) (b : β) : Environment :=
  ext.ext.addEntry env (Entry.global b)

def ScopedEnvExtension.addScopedEntry (ext : ScopedEnvExtension α β σ) (env : Environment) (namespaceName : Name) (b : β) : Environment :=
  ext.ext.addEntry env (Entry.«scoped» namespaceName b)

/-- The following function is used to implement `end_local_scope` command.

By default, all states have `delimitsLocal` set to `true`, and the following code modifies only the top element of the stack.
If the top element’s `delimitsLocal` is `false`, the function instead traverses down the stack until it reaches the first state where `delimitsLocal` is `true`.
Intuitively, `delimitsLocal` of each `State` determines whether local entries are delimited. When set to false, it allows traversal through implicit scopes where local entries are not delimited.
-/
def stateStackModify (ext : ScopedEnvExtension α β σ) (states : List (State σ)) (b : β) : List (State σ) :=
  match states with
  | [] => states
  | top :: states =>
    let top := { top with state := ext.descr.addEntry top.state b }
    let bot := if top.delimitsLocal then states else stateStackModify ext states b
    top :: bot

def ScopedEnvExtension.addLocalEntry (ext : ScopedEnvExtension α β σ) (env : Environment) (b : β) : Environment :=
  ext.ext.modifyState (asyncMode := .local) env fun s =>
    {s with stateStack := stateStackModify ext s.stateStack b}

def ScopedEnvExtension.addCore (env : Environment) (ext : ScopedEnvExtension α β σ) (b : β) (kind : AttributeKind) (namespaceName : Name) : Environment :=
  match kind with
  | AttributeKind.global => ext.addEntry env b
  | AttributeKind.local  => ext.addLocalEntry env b
  | AttributeKind.scoped => ext.addScopedEntry env namespaceName b

def ScopedEnvExtension.add [Monad m] [MonadResolveName m] [MonadEnv m] (ext : ScopedEnvExtension α β σ) (b : β) (kind := AttributeKind.global) : m Unit := do
  let ns ← getCurrNamespace
  modifyEnv (ext.addCore · b kind ns)

/-- PaperLean: `ScopedEnvExtension.getState` while this thread records environment accesses (below). -/
@[extern "lean_paperlean_scoped_state_recorded"]
private opaque recordStateOwned {α β σ : Type} [Inhabited σ] (ext : ScopedEnvExtension α β σ)
    (env : Environment) (asyncMode : EnvExtension.AsyncMode) : σ

-- (its parameters are borrowed, so that the inferred calling convention stays upstream's)
@[noinline] private def recordState {α β σ : Type} (inst : @& Inhabited σ)
    (ext : @& ScopedEnvExtension α β σ) (env : @& Environment)
    (asyncMode : @& EnvExtension.AsyncMode) : σ :=
  @recordStateOwned α β σ inst ext env asyncMode

-- PaperLean: (not inlined: its body calls PaperLean's code)
@[noinline] def ScopedEnvExtension.getState [Inhabited σ] (ext : ScopedEnvExtension α β σ)
    (env : Environment) (asyncMode := ext.ext.toEnvExtension.asyncMode) : σ :=
  -- PaperLean: recorded as the top scope's state (`Lean.PaperLean.EnvDeps`), which entering and
  -- leaving a scope keep, while they rebuild the stack around it
  (PaperLean.recordingPath ext).select (recordState inferInstance ext env asyncMode) <|
  match ext.ext.getState (asyncMode := asyncMode) env |>.stateStack with
  | top :: _ => top.state
  | _        => unreachable!

private unsafe def recordStateCore {α β σ : Type} (inst : Inhabited σ)
    (ext : ScopedEnvExtension α β σ) (env : Environment) (asyncMode : EnvExtension.AsyncMode)
    (_ : Unit) : σ :=
  have : Inhabited σ := inst
  let s := PaperLean.envWithoutRecording fun _ => ext.getState env asyncMode
  PaperLean.envRecord (.ext ext.ext.toEnvExtension.idx 100 .anonymous) (unsafeCast
    fun (env' : Environment) (_ : Name) (_ : NonScalar) =>
      ptrEq (PaperLean.envWithoutRecording fun _ => ext.getState env' asyncMode) s) s

-- (the read and its record count no heartbeats; at one type: the `extern` above has no parameters for
-- the types, an `export` would)
@[export lean_paperlean_scoped_state_recorded]
private unsafe def recordStateImpl (inst : Inhabited NonScalar)
    (ext : ScopedEnvExtension NonScalar NonScalar NonScalar) (env : Environment)
    (asyncMode : EnvExtension.AsyncMode) : NonScalar :=
  PaperLean.uncounted5 recordStateCore inst ext env asyncMode ()

def ScopedEnvExtension.activateScoped (ext : ScopedEnvExtension α β σ) (env : Environment) (namespaceName : Name) : Environment :=
  ext.ext.modifyState (asyncMode := .local) env fun s =>
    match s.stateStack with
    | top :: stack =>
      if top.activeScopes.contains namespaceName then
        s
      else
        let activeScopes := top.activeScopes.insert namespaceName
        let top :=
          match s.scopedEntries.map.find? namespaceName with
          | none =>
            { top with activeScopes := activeScopes }
          | some bs => Id.run do
            let mut state := top.state
            for b in bs do
              state := ext.descr.addEntry state b
            { state := state, activeScopes := activeScopes }
        { s with stateStack := top :: stack }
    | _ => s

def ScopedEnvExtension.modifyState (ext : ScopedEnvExtension α β σ) (env : Environment) (f : σ → σ) : Environment :=
  ext.ext.modifyState env fun s =>
    match s.stateStack with
    | top :: stack => { s with stateStack := { top with state := f top.state } :: stack }
    | _ => s

def pushScope [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] : m Unit := do
  for ext in (← scopedEnvExtensionsRef.get) do
    modifyEnv ext.pushScope

def popScope [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] : m Unit := do
  for ext in (← scopedEnvExtensionsRef.get) do
    modifyEnv ext.popScope

/-- Used to implement `end_local_scope` command, that disables delimiting local entries of ScopedEnvExtension
across `depth` scope levels.
-/
def setDelimitsLocal [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] (depth : Nat) : m Unit := do
  for ext in (← scopedEnvExtensionsRef.get) do
    modifyEnv (ext.setDelimitsLocal · depth)

def activateScoped [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] (namespaceName : Name) : m Unit := do
  for ext in (← scopedEnvExtensionsRef.get) do
    modifyEnv (ext.activateScoped · namespaceName)

abbrev SimpleScopedEnvExtension (α : Type) (σ : Type) := ScopedEnvExtension α α σ

structure SimpleScopedEnvExtension.Descr (α : Type) (σ : Type) where
  name           : Name := by exact decl_name%
  addEntry       : σ → α → σ
  initial        : σ
  finalizeImport : σ → σ := id
  exportEntry?   : Environment → α → OLeanEntries (Option α) := fun _ a => .uniform (some a)

def registerSimpleScopedEnvExtension (descr : SimpleScopedEnvExtension.Descr α σ) : IO (SimpleScopedEnvExtension α σ) := do
  registerScopedEnvExtension {
    name           := descr.name
    mkInitial      := return descr.initial
    addEntry       := descr.addEntry
    toOLeanEntry   := id
    ofOLeanEntry   := fun _ a => return a
    finalizeImport := descr.finalizeImport
    exportEntry?   := descr.exportEntry?
  }

end Lean
-- Modified by PaperLean.
