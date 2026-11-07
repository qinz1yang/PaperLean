/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lake.Build.Context

namespace Lake.PaperLean

/-- Resources belonging to live Lake runs. Lake allocates a fresh job queue for each
run. Jobs share their owner's resource only in the workspace that registered it. -/
public structure BuildSessions (α : Type) where
  private entries : IO.Ref (List (BuildContext × α))
  deriving Nonempty

@[inline] public def BuildSessions.new : BaseIO (BuildSessions α) := return ⟨← IO.mkRef []⟩

/-- Whether any run currently owns a resource of this kind. -/
public def BuildSessions.any (self : BuildSessions α) : BaseIO Bool := return !(← self.entries.get).isEmpty

private def sameRun (a b : BuildContext) : Bool :=
  unsafe ptrEq a.registeredJobs b.registeredJobs

public def BuildSessions.insert (self : BuildSessions α) (ctx : BuildContext) (value : α) : BaseIO Unit :=
  self.entries.modify ((ctx, value) :: ·)

/-- Install a resource only for the first bracket of an owner. A nested caller
cannot replace it or become responsible for its retirement. -/
public def BuildSessions.insertFresh (self : BuildSessions α) (ctx : BuildContext) (value : α) : BaseIO Bool :=
  self.entries.modifyGet fun xs =>
    if xs.any (fun e => sameRun ctx e.1) then (false, xs) else (true, (ctx, value)::xs)

public def BuildSessions.find? (self : BuildSessions α) (ctx : BuildContext) : BaseIO (Option α) := do
  return (← self.entries.get).findSome? fun (owner, value) =>
    if sameRun owner ctx && (unsafe ptrEq owner.opaqueWs ctx.opaqueWs) then some value else none

/-- Used when a changed workspace must invalidate previously recorded information in its run. -/
public def BuildSessions.findRun? (self : BuildSessions α) (ctx : BuildContext) : BaseIO (Option α) := do
  return (← self.entries.get).findSome? fun (owner, value) =>
    if sameRun owner ctx then some value else none

public def BuildSessions.take? (self : BuildSessions α) (ctx : BuildContext) : BaseIO (Option α) :=
  self.entries.modifyGet fun xs =>
    let mine := fun (e : BuildContext × α) => sameRun e.1 ctx
    ((xs.find? mine).map (·.2), xs.eraseP mine)

/-- Compatibility for an operation without a build context. It may see an explicitly
started standalone resource or the single active run, but not a sibling’s resource. -/
public def BuildSessions.singleOr? (self : BuildSessions α) (standalone : Option α) : BaseIO (Option α) := do
  match ← self.entries.get with
  | [] => return standalone
  | [(_, value)] => return some value
  | _ => return none

/-- A state cell guarded by Lean’s runtime mutex. Lake’s foundational modules need
this primitive without importing the higher-level Std synchronization API into users. -/
private opaque lockType : NonemptyType.{0}
public def RuntimeLock : Type := lockType.type
private instance : Nonempty RuntimeLock := lockType.property
@[export lean_io_basemutex_new, extern "lean_io_basemutex_new"] private opaque newLock : BaseIO RuntimeLock
@[export lean_io_basemutex_lock, extern "lean_io_basemutex_lock"] private opaque lock (mutex : @& RuntimeLock) : BaseIO Unit
@[export lean_io_basemutex_unlock, extern "lean_io_basemutex_unlock"] private opaque unlock (mutex : @& RuntimeLock) : BaseIO Unit

public structure BuildMutex (α : Type) where private mk ::
  private gate : RuntimeLock
  private state : IO.Ref α
  deriving Nonempty

@[inline] public def BuildMutex.new (initial : α) : BaseIO (BuildMutex α) :=
  return ⟨← newLock, ← IO.mkRef initial⟩

public def BuildMutex.get (mutex : BuildMutex α) : BaseIO α := mutex.state.get

public def BuildMutex.atomically [Monad m] [MonadLiftT BaseIO m] [MonadFinally m]
    (mutex : BuildMutex α) (act : StateRefT' IO.RealWorld α m β) : m β := do
  lock mutex.gate
  try act mutex.state finally unlock mutex.gate

end Lake.PaperLean
