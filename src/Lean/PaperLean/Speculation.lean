/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Init.System.IO
public import Lean.PaperLean.Base
public import Std.Data.HashMap.Basic
import Init.Data.ToString.Macro
import Init.Data.ToString.Name

-- (no `SizeOf` instances for PaperLean's types: an instance of a module of `Lean` would be one of
-- every environment that imports it, which Lean's searches would try)
set_option genSizeOf false
set_option genInjectivity false

public section

/-!
The switches of reuse.

`lean` reuses results (`Lean.PaperLean.TCCache`, `Lean.PaperLean.SectionVars`) only when a `paperlean`
command asks for it (`reuse`), and only on the threads that elaborate commands in order
(`onElabThread`), for the module of the process: its first frontend. A further frontend in the process,
which a command or a program started, turns reuse and the oracle off with a message
(`noteFrontend`). A plain `lean`, as under a plain `lake build`, runs Lean's path.

With `PAPERLEAN_REUSE_ORACLE`, a testing switch, each reuse of a typeclass result
(`Lean.PaperLean.TCCache`) is compared with Lean's own search, and each reuse of section variables
(`Lean.PaperLean.SectionVars`) with Lean's elaboration. A difference is a defect of PaperLean:
`lean` says what differs and fails at once (`fail`).
-/

namespace Lean.PaperLean.Speculation

/-- Whether this `lean` reuses results: a `paperlean` command asked for it (`PAPERLEAN_REUSE=1`, which
`Lake.PaperLean.BuildEnv.leanEnv` sets for the `lean` processes of its builds), and not
`PAPERLEAN_EXACT`. -/
builtin_initialize reuse : Bool ← do
  return (← IO.getEnv "PAPERLEAN_REUSE") == some "1" && (← IO.getEnv "PAPERLEAN_EXACT").isNone

/-- Whether each reuse is also compared with Lean's own elaboration (`PAPERLEAN_REUSE_ORACLE`, for
testing). -/
builtin_initialize reuseOracle : Bool ← do
  return reuse && (← IO.getEnv "PAPERLEAN_REUSE_ORACLE").isSome

/-- A fault asked for, for testing the oracles (`PAPERLEAN_REUSE_FAULT`: `stale-cache` keeps the entries
of Lean's caches under their earlier keys when a reuse of section variables renames these,
`stale-fun-info` those of the cache of `funInfo`, `tc-names` counts one name too many for a reuse of a
typeclass result). -/
private builtin_initialize faultAsked : String ← return (← IO.getEnv "PAPERLEAN_REUSE_FAULT").getD ""

/-- The fault to put in a reuse: none unless the oracle that is to find it runs. -/
def fault : String :=
  if reuseOracle then faultAsked else ""

/-- Sets whether this thread elaborates commands in order (`onElabThread`). -/
@[extern "lean_paperlean_set_elab_thread"]
opaque setElabThread (on : Bool) : BaseIO Unit

/-- Whether this thread elaborates commands in order and may use the caches of reuse, unlike the
tasks that it starts, e.g. of linters, whose order is not that of the commands. Only where
`nativeAvailable`. -/
@[extern "lean_paperlean_elab_thread"]
opaque onElabThread : BaseIO Bool

/-- Runs `act`, in which this thread uses no caches of reuse: for the oracles' run of Lean's own
elaboration. -/
def withoutReuse [Monad m] [MonadFinally m] [MonadLiftT BaseIO m] (act : m α) : m α := do
  let on ← onElabThread
  setElabThread false
  try act finally setElabThread on

/-- Why computations were not kept or results not reused, of one kind of reuse: the number of each
reason, and the position of the first (`line:column`). -/
abbrev Reasons := IO.Ref (Std.HashMap String (Nat × String))

/-- Counts `why`, with the position that `pos` gives if it is the first of its reason. -/
def Reasons.note (r : Reasons) (why : String) (pos : Unit → String) : BaseIO Unit := do
  let m ← r.get
  match m[why]? with
  | some (n, p) => r.set (m.insert why (n + 1, p))
  | none => r.set (m.insert why (1, pos ()))

/-- The reasons as `PAPERLEAN_REUSE_STATS` writes them: `why=count@position`. -/
def Reasons.render (r : Reasons) : BaseIO (List String) := do
  let m ← r.get
  return m.toList.map fun (why, n, pos) => s!"{why}={n}@{pos}"

/-- A way for a search or an elaboration to be left out of reuse altogether, whatever an earlier one
did, in the order of `exclusions`. -/
abbrev Exclusion := UInt8

/-- What the exclusions say, of typeclass results (the first `numTcExclusions`) and of section
variables. -/
private def exclusions : Array String := #[
  "not on the thread that elaborates commands in order, e.g. in a proof",
  "trace options or diagnostics",
  "a custom unfolding predicate",
  "tracked or chosen let-variables",
  "metavariables in the problem or in its context",
  "in `grind`, under a name generator that starts again",
  "not on the thread that elaborates commands in order",
  "trace options or diagnostics",
  "in the elaboration of a declaration in the background",
  "the state is not that of the start of a command"]

private def numTcExclusions := 6

@[extern "lean_paperlean_note_exclusion"]
private opaque noteExclusionCore (kind : Exclusion) : BaseIO Bool

@[extern "lean_paperlean_exclusions"]
private opaque exclusionCount (kind : Exclusion) : BaseIO Nat

/-- The position of the first of each exclusion that happened, `line:column`. -/
private builtin_initialize exclusionPosRef : IO.Ref (List (UInt8 × String)) ← IO.mkRef []

/-- Counts a search or an elaboration left out in the way `kind`, on any thread, with the position
that `pos` gives if it is the first. -/
def noteExclusion (kind : Exclusion) (pos : Unit → String) : BaseIO Unit := do
  if ← noteExclusionCore kind then
    exclusionPosRef.modify (List.cons (kind, pos ()))

/-- The exclusions as `PAPERLEAN_REUSE_STATS` writes them (`Reasons.render`), of typeclass results if
`tc`, else of section variables. -/
def renderExclusions (tc : Bool) : BaseIO (List String) := do
  let pos ← exclusionPosRef.get
  let mut out := []
  let mut i := 0
  for what in exclusions do
    if (i < numTcExclusions) == tc then
      let n ← exclusionCount i.toUInt8
      if n > 0 then
        let p := (pos.lookup i.toUInt8).getD "0:0"
        out := s!"not eligible: {what}={n}@{p}" :: out
    i := i + 1
  return out

/-- Says that a reuse differs from Lean's elaboration and ends the process with a failure. -/
@[extern "lean_paperlean_speculation_fail"]
opaque fail (reason : @& String) : BaseIO Unit

@[extern "lean_paperlean_note_frontend"]
private opaque noteFrontendCore (fileName : @& String) : BaseIO Unit

/-- Notes a frontend run of `fileName`: from the second of the process on, nothing is reused any more,
which it says on the standard error. -/
@[noinline] def noteFrontend (fileName : String) : BaseIO Unit := do
  if reuse then noteFrontendCore fileName

/-- Stops a registration of a builtin (`KeyedDeclsAttribute.addBuiltin`) other than while `initializing`
(`Lean.initializing`: also the initializers of imported modules, e.g. of Lake's builtin elaborators in
a precompiled module), which is not normal code. -/
@[noinline] def checkBuiltinRegistration (declName : Name) (initializing : Bool) : IO Unit := do
  if nativeAvailable declName && reuse && !initializing then
    throw <| .userError s!"PaperLean does not support registering a builtin at run time \
      ({declName}); build this file with `lake build`"

end Lean.PaperLean.Speculation
