/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lake.Build.Infos
public import Lake.Build.Store
public import Lake.PaperLean.BuildSessions
import Std.Data.HashMap.Basic
import Init.While

namespace Lake.PaperLean.SetupProviders

/-- Providers whose answers determine the setup import graph and file paths. -/
public def facets : Array Lean.Name :=
  #[Module.inputFacet, Module.headerFacet, Module.importInfoFacet,
    Module.presetupFacet, Module.leanArtsFacet, Module.exportInfoFacet]

public structure Observers where
  input : Module → ModuleInput → BaseIO Unit
  exports : Module → ModuleExportInfo → BaseIO Unit

set_option genSizeOf false in
private structure Seen where
  input : Bool := false
  exports : Bool := false
  headers : Bool := false
  closure : Bool := false

private structure State where
  enabled : Bool := false
  store? : Option (IO.Ref BuildStore) := none
  snapshot : BuildStore := BuildStore.empty
  observers? : Option Observers := none
  coverage? : Option (BuildMutex (Std.HashMap BuildKey Seen)) := none
  canonical : Module → Bool := fun _ => false
  -- Module and library wrappers are reconstructed by Lake. Retain the identities
  -- of the package and configuration behind each validated package-module key.
  modules : Std.HashMap BuildKey Module := {}
  -- Keep the dispatch closures alive while their addresses are in use.
  fetchers : Std.HashMap USize NonScalar := {}

private initialize sessions : BuildSessions (BuildMutex State) ← BuildSessions.new

public def beginRun (ctx : BuildContext) (enabled : Bool) (canonical : Module → Bool)
    (observers : Observers) : BaseIO Unit := do
  -- The setup/launch registry separately brackets every public runner. This
  -- witness registry contains only owners whose real compiles can use the index.
  if enabled then
    let coverage ← BuildMutex.new (∅ : Std.HashMap BuildKey Seen)
    sessions.insert ctx (← BuildMutex.new { enabled, canonical, observers? := some observers, coverage? := some coverage })

public def endRun (ctx : BuildContext) : BaseIO Unit :=
  discard <| sessions.take? ctx

-- Demote the issuing run even when the caller immediately restores its workspace.
private def findSession (ctx : BuildContext) : BaseIO (Option (BuildMutex State)) := do
  if let some session ← sessions.find? ctx then
    return if (← session.get).enabled then some session else none
  if let some owner ← sessions.findRun? ctx then
    if (← owner.get).enabled then owner.atomically (set ({} : State))
  return none

/-- Choose the recursive dispatcher for this owner. A context derived from a
tracked run cannot suppress its checks by changing the local no-build flag. -/
public def observing (ctx : BuildContext) : BaseIO Bool := return (← findSession ctx).isSome

private def State.checkStore (s : State) (ref : IO.Ref BuildStore) (actual : BuildStore) : State :=
  if !s.enabled then s else
  match s.store? with
  | none => if actual.isEmpty then {s with store? := some ref, snapshot := actual} else {}
  | some expected => if unsafe ptrEq ref expected && ptrEq actual s.snapshot then s else {}

private def sameModule (a b : Module) : Bool :=
  a.lib.name == b.lib.name && (unsafe ptrEq a.pkg b.pkg) &&
    (unsafe ptrAddrUnsafe a.lib.config == ptrAddrUnsafe b.lib.config)

private def State.knownModule (s : State) (mod : Module) : Bool :=
  s.modules[mod.key]?.any (sameModule · mod)

private def State.checkModule (s : State) (key : BuildKey) (mod : Module) : State := Id.run do
  unless s.enabled do return s
  unless key == mod.key do return {}
  if let some expected := s.modules[key]? then
    if sameModule expected mod then return s
    return {}
  unless s.canonical mod do return {}
  return { s with modules := s.modules.insert key mod }

private def State.checkPayload (s : State) (info : BuildInfo) : State :=
  match info with
  | .facet target kind data _ => if h : kind = Module.facetKind then
      s.checkModule target (cast (by simp [h]) data)
    else {}
  | _ => s

/-- Remember the recursive dispatcher supplied by the standard build engine to a
module provider. A custom dispatcher may answer calls that evaluating an index would skip. -/
public def enterProvider (ctx : BuildContext) (ref : IO.Ref BuildStore) (info : BuildInfo)
    (fetch : α) (keepFetcher : Bool) : BaseIO Unit := do
  let some session ← findSession ctx | return
  session.atomically do
    let s := ((← get).checkStore ref (← ref.get)).checkPayload info
    if s.enabled && keepFetcher then
      let address := unsafe ptrAddrUnsafe fetch
      let fetchers := s.fetchers.insertIfNew address (unsafe unsafeCast fetch)
      set { s with fetchers }
    else set s

/-- Install Lake's original job and advance the store witness atomically. The
snapshot is the source of completed inputs and exports at an actual setup lookup;
normal fetches do not create dependent tasks or run observations. -/
public def storeJob (ctx : BuildContext) (ref : IO.Ref BuildStore) (info : BuildInfo)
    (job : Job (BuildData info.key)) : BaseIO (Job (BuildData info.key)) := do
  let some session ← findSession ctx | do
    ref.modify (·.insert info.key job)
    return job
  session.atomically do
    let (before, after) ← ref.modifyGet fun store =>
      let next := store.insert info.key job
      ((store, next), next)
    let s := (← get).checkStore ref before
    set <| if s.enabled && !before.contains info.key then {s with snapshot := after} else {}
  return job

private def State.verifyResult (s : State) (ref : IO.Ref BuildStore) (actual : BuildStore)
    (info : BuildInfo) (job : Job (BuildData info.key)) : State :=
  let s := (s.checkStore ref actual).checkPayload info
  if s.enabled && !(s.snapshot.get? info.key).any (fun (stored : Job (BuildData info.key)) =>
      unsafe ptrEq stored.task job.task) then {} else s

/-- Accept a result from the memoized dispatcher if its store and module still match.
A cache hit with an already validated payload needs no change to the session. Additions
and invalidations recheck the current snapshot while holding its update lock. -/
public def checkResult (ctx : BuildContext) (ref : IO.Ref BuildStore) (info : BuildInfo)
    (job : Job (BuildData info.key)) : BaseIO Unit := do
  unless ← sessions.any do return
  let .facet _ _ _ facet := info | return
  unless facets.contains facet do return
  let some session ← findSession ctx | return
  let seen ← session.get
  if unsafe ptrEq seen (seen.verifyResult ref (← ref.get) info job) then return
  session.atomically do set <| (← get).verifyResult ref (← ref.get) info job

/-- Seeds of the optional header planner, only for jobs the dispatcher already knows. -/
public def activeModules (ctx : BuildContext) : BaseIO (Array Lean.Name) := do
  let some guard ← findSession ctx | return #[]
  return (← guard.get).modules.fold (fun names _ mod => names.push mod.name) #[]

private def finished? (job? : Option (Job α)) : BaseIO (Option α) := do
  let some job := job? | return none
  unless ← IO.hasFinished job.task do return none
  return job.task.get.result?

private abbrev ObserveM := StateRefT' IO.RealWorld (Std.HashMap BuildKey Seen) BaseIO

private def exportReady (snap : State) (observers : Observers) (mod : Module) : ObserveM Bool := do
  let known := (← get).getD mod.key {}
  if known.exports then return true
  let job : Option (Job ModuleExportInfo) := cast (by simp) (snap.snapshot.get? mod.exportInfo.key)
  let some info ← finished? job | return false
  observers.exports mod info
  modify (·.insert mod.key {known with exports := true})
  return true

set_option genSizeOf false in
private inductive Frame where
  | enter (mod : Module) (needsExport : Bool)
  | finish (key : BuildKey)

/-- Inspect only selected, successful jobs that have already finished. A parent's
index needs every child's export, including when that child was a previous root and
its own export could not yet exist. Readiness is monotone while the store is certified.
The explicit legacy graph query needs only input records. -/
private def collect (snap : State) (observers : Observers) (root : Module) (withExports : Bool) : ObserveM Bool := do
  let mut todo := #[Frame.enter root false]
  let mut active : Std.HashSet BuildKey := {}
  while let some frame := todo.back? do
    todo := todo.pop
    match frame with
    | .finish key =>
      active := active.erase key
      let old := (← get).getD key {}
      modify (·.insert key {old with headers := true, closure := old.closure || withExports})
    | .enter mod needsExport =>
      if needsExport then
        unless ← exportReady snap observers mod do return false
      let key := mod.key
      let old := (← get).getD key {}
      if (if withExports then old.closure else old.headers) then continue
      if active.contains key then return false
      let job : Option (Job ModuleInput) := cast (by simp) (snap.snapshot.get? mod.input.key)
      let some input ← finished? job | return false
      if !old.input then
        observers.input mod input
        modify (·.insert key {old with input := true})
      active := active.insert key
      todo := todo.push (.finish key)
      for imp in input.imports.reverse do
        if let some child := imp.module? then
          if !(snap.knownModule child) then return false
          todo := todo.push (.enter child withExports)
  return true

/-- Verification before and after observing runs on the store lock; the possibly
large graph traversal does not. Builders can append memoized jobs meanwhile. A
replaced store, module payload, dispatcher or job permanently invalidates this run. -/
private def prepare (ctx : BuildContext) (mod : Module) (consumer? : Option (IO.Ref BuildStore × USize)) :
    BaseIO Bool := do
  let some session ← findSession ctx | return false
  let check := session.atomically do
    let s ← get
    unless s.enabled do return none
    let some ref := consumer?.map Prod.fst <|> s.store? | return none
    let s := (s.checkStore ref (← ref.get)).checkModule mod.key mod
    if !s.enabled || consumer?.any (fun p => !s.fetchers.contains p.2) then
      set ({} : State)
      return none
    set s
    return some s
  let some snap ← check | return false
  let some observers := snap.observers? | return false
  let some coverage := snap.coverage? | return false
  unless ← coverage.atomically (collect snap observers mod consumer?.isSome) do return false
  return (← check).isSome

/-- Explicit legacy index lookup consults the authentic run captured by its index
registry, and only needs selected input rows. It never starts an input job. -/
public def prepareStored (ctx : BuildContext) (mod : Module) : BaseIO Bool :=
  prepare ctx mod none

/-- The public moved-artifact query also includes completed jobs for modules not
visited by an index request. Ordinary compilation already checked the exports of
its own closure and can read its recorded overrides directly. -/
public def observeExports (ctx : BuildContext) : BaseIO Unit := do
  let some session ← findSession ctx | return
  let snap ← session.atomically do
    let s ← get
    let some store := s.store? | return none
    let s := s.checkStore store (← store.get)
    set s
    return if s.enabled then some s else none
  let some s := snap | return
  let some observers := s.observers? | return
  let some coverage := s.coverage? | return
  coverage.atomically do
    for (_, mod) in s.modules do discard <| exportReady s observers mod


/-- At the consumer, certify the actual selected jobs and dispatcher before omitting lookups. -/
public def mayIndex (ctx : BuildContext) (ref : IO.Ref BuildStore) (fetch : α) (mod : Module) : BaseIO Bool :=
  prepare ctx mod (some (ref, unsafe ptrAddrUnsafe fetch))

end Lake.PaperLean.SetupProviders
