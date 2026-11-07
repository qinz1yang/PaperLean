/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lake.Config.Module
public import Lake.PaperLean.BuildSessions
import Lake.PaperLean.Env
import Lean.PaperLean.System
import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic

/-!
Critical-path-first order of compiles for builds under `paperlean` commands (`accelerated`). Lake
compiles a module as soon as its imports are built, in the order in which modules become ready. Here
a module that compiles first waits for one of as many slots as Lean's task manager has threads
(`Lake.Module.recBuildLean`), and a slot that becomes free goes to the module with the longest path
from it to the end of the build (its bottom level): through the modules that import it, in the import
graph that the build has read so far (`noteModule`), with the compile times that earlier builds
recorded (`.lake/paperlean-times.paperlean`), or else estimates from the sizes of their sources. The
candidates are the modules waiting and those about to: those with a job (`register`) all of whose
imports are done, one of which compiled; a slot is kept for such a module until it asks for it, its
job ends, or `keepFor` passes, once per module. Every module with a job is settled when that job
ends, however it ends (`settleAfter`). The order of compiles does not change what a module compiles
to. A record that is missing, damaged, or of another build is ignored; `PAPERLEAN_SCHEDULE=0` turns
this off, and `PAPERLEAN_SCHEDULE_SLOTS` and `PAPERLEAN_SCHEDULE_KEEP` set the number of slots and
`keepFor` (for tests: on a busy machine a module may take longer than `keepFor` to ask for its slot,
which then goes to the next one, so that the order of compiles depends on the load).

The state is shared by the build's threads, which makes Lean copy an array on every change; so the
graph only changes when a slot is to be given (`drain`), with the events since, at most twice per
compile, and a build that compiles nothing does not build it. After the build (`finish`) the state
is closed: whatever still refers to it does nothing.
-/

open System Lean

namespace Lake.PaperLean.Schedule

/-- A module, by its package (`Package.keyName`) and name: names repeat across packages. -/
abbrev Key := Name × Name

/-- The key of the module `mod`. -/
@[inline] def keyOf (mod : Module) : Key := (mod.pkg.keyName, mod.name)

/-- The name of `mod` in the record of compile times. -/
private def recordName (mod : Module) : String := s!"{mod.pkg.baseName}/{mod.name}"

/-- A change to the graph, applied by `drain`. -/
inductive Event where
  | note (mod : Key) (imports : Array Key) (weight : Nat)
  | registered (mod : Key)
  | compiled (mod : Key)
  | finished (mod : Key) (ok : Bool)

structure State where
  keepMs : UInt32 := 50
  /-- Set by `finish`. -/
  closed : Bool := false
  /-- The number of slots that are free and not kept for a module. -/
  free : Nat
  /-- The events not applied yet, the latest first. -/
  events : List Event := []
  /-- The modules seen so far. -/
  index : Std.HashMap Key Nat := {}
  /-- Per module: its estimated compile time (ms), if noted. -/
  weight : Array (Option Nat) := #[]
  /-- Per module: the modules that import it. -/
  importers : Array (Array Nat) := #[]
  /-- Per module: the number of its imports whose job is not done yet. -/
  missing : Array Nat := #[]
  /-- Per module: whether it has a job in this build; whether that job is done; whether it compiled;
  whether it imports a module that compiled; whether it asked for a slot; whether a slot was kept for
  it. -/
  registered : Array Bool := #[]
  done : Array Bool := #[]
  compiled : Array Bool := #[]
  importsCompiled : Array Bool := #[]
  requested : Array Bool := #[]
  wasKept : Array Bool := #[]
  /-- Changes whenever the graph does. -/
  version : Nat := 1
  /-- Per module: its bottom level plus one, or zero if not computed for `memoVersion`. -/
  memo : Array Nat := #[]
  memoVersion : Nat := 0
  /-- The modules waiting for a slot. -/
  waiting : Array (Nat × IO.Promise Unit) := #[]
  /-- The modules about to ask for a slot (`checkComing`). -/
  coming : Std.HashSet Nat := {}
  /-- The modules of `coming` for which a slot is kept, and the modules that hold a slot. -/
  kept : Std.HashSet Nat := {}
  holding : Std.HashSet Nat := {}
  /-- The modules whose job runs up to its compile, which it does not do then (`beginDry`), and those
  of them that reached it. -/
  dry : Std.HashSet Key := {}
  deferred : Std.HashSet Key := {}
  /-- Compile times recorded by earlier builds, by `recordName`. -/
  times : Std.HashMap String Nat := {}
  /-- Compile times measured in this build. -/
  measured : List (String × Nat) := []
  file : FilePath
  deriving Inhabited

/-- The scheduler of a single build, shared by exactly that build’s jobs. -/
public structure Session where
  private state? : Option (IO.Ref State) := none
  deriving Inhabited

/-- A queue is freshly allocated for each Lake runner. A custom job can also replace
the workspace in its build context; in that case it uses ordinary Lake scheduling. -/
private initialize sessions : BuildSessions Session ← BuildSessions.new
private initialize standalone : IO.Ref Session ← IO.mkRef {}

/-- Returns the scheduler that registered this job, or an inactive session. -/
public def sessionFor (ctx : BuildContext) : BaseIO Session := do
  return (← sessions.find? ctx).getD {}

/-- The legacy standalone API can also observe an unambiguous active workspace build. -/
private def currentSession : BaseIO Session := do
  return (← sessions.singleOr? (some (← standalone.get))).getD {}

/-- The first line of the record: its format, and the version and build of PaperLean and Lean's
commit that wrote it. -/
private def header : String :=
  s!"paperlean-times 2 {Lean.PaperLean.version}+{Lean.PaperLean.build} {Lean.githash}"

/-- The compile times that `text` records, if this build wrote it: `header`, then a line per module
with the time (ms) and `recordName`. -/
private def parseTimes (text : String) : Std.HashMap String Nat := Id.run do
  let lines := text.split '\n' |>.toStringList
  if lines.head? != some header then return {}
  let mut out := {}
  for line in lines.drop 1 do
    match line.split ' ' |>.toStringList with
    | ms :: rest@(_ :: _) =>
      if let some t := ms.toNat? then out := out.insert (" ".intercalate rest) t
    | _ => pure ()
  return out

/-- The record of the workspace in `wsDir`. -/
public def recordFile (wsDir : FilePath) : FilePath := wsDir / ".lake" / "paperlean-times.paperlean"

/-- The number of threads of Lean's task manager (`LEAN_NUM_THREADS`, else the hardware's). -/
private def poolSize : BaseIO Nat := do
  if let some n := (← IO.getEnv "LEAN_NUM_THREADS").bind (·.toNat?) then
    if n > 0 then return n
  return max 1 (System.Platform.Internal.getHardwareConcurrency ()).toNat

/-- Starts scheduling at the start of a build of the workspace in `wsDir` under a `paperlean` command
(`accelerated`). -/
private def newSession (wsDir : FilePath) : BaseIO Session := do
  unless ← accelerated do return {}
  if (← IO.getEnv "PAPERLEAN_SCHEDULE") == some "0" then return {}
  let slots ← match (← IO.getEnv "PAPERLEAN_SCHEDULE_SLOTS").bind (·.toNat?) with
    | some n => pure (max 1 n)
    | none => poolSize
  let keepMs := ((← IO.getEnv "PAPERLEAN_SCHEDULE_KEEP").bind (·.toNat?)).getD 50
  let file := recordFile wsDir
  let times ← if ← isSpecialFile file then pure {} else
    match ← (IO.FS.readFile file).toBaseIO with
    | .ok text => pure (parseTimes text)
    | .error _ => pure {}
  return ⟨some (← IO.mkRef {free := slots, keepMs := keepMs.toUInt32, times, file})⟩

public def startFor (ctx : BuildContext) (wsDir : FilePath) (enable := true) : BaseIO Session := do
  let session ← if enable then newSession wsDir else pure {}
  sessions.insert ctx session
  return session

public def Session.active (session : Session) : Bool := session.state?.isSome

/-- The estimated compile time (ms) of a module whose source has `bytes` bytes, by a fit to the
compile times of Mathlib's modules. -/
private def estimate (bytes : Nat) : Nat := 390 + bytes * 43 / 1000

private def nodeOf (k : Key) (s : State) : Nat × State :=
  match s.index[k]? with
  | some i => (i, s)
  | none =>
    let i := s.weight.size
    (i, { s with index := s.index.insert k i, weight := s.weight.push none,
                 importers := s.importers.push #[], missing := s.missing.push 0,
                 registered := s.registered.push false, done := s.done.push false,
                 compiled := s.compiled.push false, importsCompiled := s.importsCompiled.push false,
                 requested := s.requested.push false, wasKept := s.wasKept.push false,
                 version := s.version + 1 })

/-- Adds module `j` to `coming` if it is about to ask for a slot: it has a job, which has not asked
for one and is not done, and all of its imports are done, one of which compiled. -/
private def checkComing (j : Nat) (s : State) : State :=
  if s.registered[j]! && s.missing[j]! == 0 && s.importsCompiled[j]! && !s.done[j]! &&
      !s.requested[j]! then
    { s with coming := s.coming.insert j }
  else s

private def apply (s : State) : Event → State
  | .note k imports w => Id.run do
    let (i, s) := nodeOf k s
    if s.weight[i]!.isSome then return s
    let mut s := { s with weight := s.weight.set! i (some w), version := s.version + 1 }
    let mut seen : Std.HashSet Key := {}
    for imp in imports do
      if seen.contains imp then continue
      seen := seen.insert imp
      let (j, s') := nodeOf imp s
      s := { s' with importers := s'.importers.modify j (·.push i) }
      if !s.done[j]! then s := { s with missing := s.missing.modify i (· + 1) }
      if s.compiled[j]! then s := { s with importsCompiled := s.importsCompiled.set! i true }
    return checkComing i s
  | .registered k =>
    let (i, s) := nodeOf k s
    checkComing i { s with registered := s.registered.set! i true }
  | .compiled k =>
    let (i, s) := nodeOf k s
    { s with compiled := s.compiled.set! i true }
  | .finished k ok => Id.run do
    let (i, s) := nodeOf k s
    if s.done[i]! then return s
    let mut s := { s with done := s.done.set! i true, coming := s.coming.erase i }
    if ok then
      for j in s.importers[i]! do
        s := { s with missing := s.missing.modify j (· - 1) }
        if s.compiled[i]! then s := { s with importsCompiled := s.importsCompiled.set! j true }
        s := checkComing j s
    return s

/-- Applies the events not applied yet. -/
private def drain (s : State) : State :=
  if s.events.isEmpty then s else
  let events := s.events
  events.foldr (fun e s => apply s e) { s with events := [] }

/-- Runs `f` on the state of this build unless there is none or it is closed. -/
@[inline] private def Session.update (session : Session) (f : State → α × State) (dflt : α) : BaseIO α := do
  let some m := session.state? | return dflt
  m.modifyGet fun s => if s.closed then (dflt, s) else f s

/-- Notes the module `mod`, whose source has `bytes` bytes, and its imports in the workspace. -/
public def Session.noteModule {α : Type} (session : Session) (mod : Module) (imports : Array α) (module? : α → Option Module)
    (bytes : Nat) : BaseIO Unit := do
  -- (the imports' modules taken here, not by `Module.recFetchInput`, whose code then specializes
  -- as official Lean's)
  unless session.active do return
  let imports := imports.filterMap module?
  session.update (dflt := ()) fun s =>
    let w := s.times[recordName mod]?.getD (estimate bytes)
    ((), { s with events := .note (keyOf mod) (imports.map keyOf) w :: s.events })

/-- Records that the module `mod` has a job in this build (`Lake.Module.recBuildLean`), which
`settleAfter` settles. -/
public def Session.register (session : Session) (mod : Module) : BaseIO Unit := do
  session.update (dflt := ()) fun s => ((), { s with events := .registered (keyOf mod) :: s.events })

/-- The bottom level of module `i`: its time plus the longest bottom level of its importers. -/
private partial def levelOf (weight : Array (Option Nat)) (importers : Array (Array Nat)) (i : Nat) :
    StateM (Array Nat) Nat := do
  let m := (← get)[i]!
  if m > 0 then return m - 1
  -- (level 0 meanwhile, against cycles, which the build reports)
  modify (·.set! i 1)
  let mut best := 0
  for j in importers[i]! do
    best := max best (← levelOf weight importers j)
  let l := (weight[i]!.getD 0) + best
  modify (·.set! i (l + 1))
  return l

/-- What `assign` did with a slot. -/
private inductive Assigned where
  | free
  | granted (p : IO.Promise Unit)
  | kept (i : Nat)

/-- Gives a slot that became free to the candidate with the longest bottom level: a waiting module,
or a coming one for which no slot was kept before, for which it is kept (in the drained state). -/
private def assign (s : State) : Assigned × State := Id.run do
  let candidates := s.coming.fold (init := #[]) fun c i =>
    if s.kept.contains i || s.wasKept[i]! then c else c.push i
  if s.waiting.isEmpty && candidates.isEmpty then return (.free, { s with free := s.free + 1 })
  let memo := if s.memoVersion == s.version then s.memo else Array.replicate s.weight.size 0
  let s := { s with memo := #[], memoVersion := s.version }
  let mut memo := memo
  -- the best waiting module by its index in `waiting`, else the best coming one
  let mut best : Nat ⊕ Nat := .inl 0
  let mut bestLevel := 0
  let mut first := true
  for h : k in [0:s.waiting.size] do
    let (l, memo') := levelOf s.weight s.importers s.waiting[k].1 |>.run memo
    memo := memo'
    if first || l > bestLevel then
      best := .inl k; bestLevel := l; first := false
  for i in candidates do
    let (l, memo') := levelOf s.weight s.importers i |>.run memo
    memo := memo'
    if first || l > bestLevel then
      best := .inr i; bestLevel := l; first := false
  let s := { s with memo }
  match best with
  | .inl k =>
    match s.waiting[k]? with
    | some (i, p) =>
      return (.granted p, { s with waiting := s.waiting.eraseIdx! k, holding := s.holding.insert i })
    | none => return (.free, { s with free := s.free + 1 })
  | .inr i =>
    return (.kept i, { s with kept := s.kept.insert i, wasKept := s.wasKept.set! i true })

/-- Assigns `n` slots that became free: the promises of the modules that got one, and the modules for
which one is kept. -/
private def assignFreed (n : Nat) (s : State) : (Array (IO.Promise Unit) × Array Nat) × State :=
  Id.run do
  let mut s := s
  let mut ps := #[]
  let mut kept := #[]
  for _ in [0:n] do
    let (a, s') := assign s
    s := s'
    match a with
    | .granted p => ps := ps.push p
    | .kept i => kept := kept.push i
    | .free => pure ()
  return ((ps, kept), s)

mutual
/-- Resolves the promises of `assignFreed` and ends the keeping of slots after `keepFor`. -/
private partial def wake (m : IO.Ref State) : Array (IO.Promise Unit) × Array Nat → BaseIO Unit
  | (ps, kept) => do
    for p in ps do p.resolve ()
    for i in kept do
      discard <| BaseIO.asTask (prio := .dedicated) do
        IO.sleep (← m.get).keepMs
        expire m i

/-- Ends keeping a slot for the module `i` if it is still kept. -/
private partial def expire (m : IO.Ref State) (i : Nat) : BaseIO Unit := do
  let r ← m.modifyGet fun s =>
    if !s.closed && s.kept.contains i then assignFreed 1 { drain s with kept := s.kept.erase i }
    else ((#[], #[]), s)
  wake m r
end

/-- Requests a slot for the module `mod`, which is about to compile: the task completes once it has
one, which goes back when its job ends (`settleAfter`). -/
public def Session.request (session : Session) (mod : Module) : BaseIO (Task Unit) := do
  let p ← IO.Promise.new
  let granted ← session.update (dflt := true) fun s =>
    let (i, s) := nodeOf (keyOf mod) (drain s)
    let s := { s with coming := s.coming.erase i, requested := s.requested.set! i true }
    if s.kept.contains i then (true, { s with kept := s.kept.erase i, holding := s.holding.insert i })
    else if s.free > 0 then (true, { s with free := s.free - 1, holding := s.holding.insert i })
    else (false, { s with waiting := s.waiting.push (i, p) })
  return if granted then .pure () else p.result!

/-- Settles the module `k` whose job ended, successfully if `ok`: gives back its slot and one kept for
it to other modules. -/
private def settle (m : IO.Ref State) (k : Key) (ok : Bool) : BaseIO Unit := do
  let r ← m.modifyGet fun s => Id.run do
    if s.closed then return ((#[], #[]), s)
    let (freed, i) := match s.index[k]? with
      | some i => ((if s.holding.contains i then 1 else 0) + (if s.kept.contains i then 1 else 0), i)
      | none => (0, 0)
    if freed == 0 then return ((#[], #[]), { s with events := .finished k ok :: s.events })
    let s := apply (drain s) (.finished k ok)
    return assignFreed freed { s with holding := s.holding.erase i, kept := s.kept.erase i }
  wake m r

/-- Settles the module `mod` once `t`, whether its job succeeded, completes, whatever the job did:
also if it failed before it ran or was cancelled. -/
public def Session.settleAfter (session : Session) (mod : Module) (t : Task Bool) : BaseIO Unit := do
  let some m := session.state? | return
  let k := keyOf mod
  discard <| BaseIO.mapTask (t := t) (sync := true) fun ok => settle m k ok

/-- Starts running the job of the module `mod` up to its compile, which it does not do then
(`deferCompile`). -/
public def Session.beginDry (session : Session) (mod : Module) : BaseIO Unit :=
  session.update (dflt := ()) fun s => ((), { s with dry := s.dry.insert (keyOf mod) })

/-- Ends `beginDry`: whether the job reached its compile. -/
public def Session.endDry (session : Session) (mod : Module) : BaseIO Bool :=
  let k := keyOf mod
  session.update (dflt := false) fun s =>
    (s.deferred.contains k, { s with dry := s.dry.erase k, deferred := s.deferred.erase k })

/-- Called before the module `mod` compiles: whether it is to stop there (`beginDry`). -/
public def Session.deferCompile (session : Session) (mod : Module) : BaseIO Bool :=
  let k := keyOf mod
  session.update (dflt := false) fun s =>
    if s.dry.contains k then (true, { s with deferred := s.deferred.insert k }) else (false, s)

/-- Records that the module `mod` compiled in `ms` milliseconds. -/
public def Session.compiled (session : Session) (mod : Module) (ms : Nat) : BaseIO Unit :=
  session.update (dflt := ()) fun s =>
    ((), { s with events := .compiled (keyOf mod) :: s.events,
                  measured := (recordName mod, ms) :: s.measured })

/-- Ends scheduling at the end of the build: closes the state, lets modules still waiting (whose jobs
the build did not wait for) go on, and writes the compile times measured, with those of earlier
builds. -/
private def Session.close (session : Session) : BaseIO Unit := do
  let some m := session.state? | return
  let s ← m.modifyGet fun s => (s, { s with closed := true, waiting := #[] })
  for (_, p) in s.waiting do p.resolve ()
  removeStaleTemps s.file
  if s.measured.isEmpty then return
  let times := s.measured.foldr (fun (n, ms) t => t.insert n ms) s.times
  let text := times.fold (init := header ++ "\n") fun out n ms => out ++ s!"{ms} {n}\n"
  discard <| (do
    if let some dir := s.file.parent then IO.FS.createDirAll dir
    publishFile s.file (·.putStr text)).toBaseIO

public def finishFor (ctx : BuildContext) (session : Session) : BaseIO Unit := do
  discard <| sessions.take? ctx
  session.close

-- Keep the standalone entry points for callers compiled against earlier releases.
public def start (wsDir : FilePath) : BaseIO Unit := do
  (← standalone.swap (← newSession wsDir)).close

public def finish : BaseIO Unit := do
  (← standalone.swap {}).close

public def active : BaseIO Bool := return (← currentSession).active

public def noteModule {α : Type} (mod : Module) (imports : Array α) (module? : α → Option Module)
    (bytes : Nat) : BaseIO Unit := do (← currentSession).noteModule mod imports module? bytes

public def register (mod : Module) : BaseIO Unit := do (← currentSession).register mod
public def request (mod : Module) : BaseIO (Task Unit) := do (← currentSession).request mod
public def settleAfter (mod : Module) (t : Task Bool) : BaseIO Unit := do
  (← currentSession).settleAfter mod t
public def beginDry (mod : Module) : BaseIO Unit := do (← currentSession).beginDry mod
public def endDry (mod : Module) : BaseIO Bool := do (← currentSession).endDry mod
public def deferCompile (mod : Module) : BaseIO Bool := do (← currentSession).deferCompile mod
public def compiled (mod : Module) (ms : Nat) : BaseIO Unit := do (← currentSession).compiled mod ms

end Lake.PaperLean.Schedule
