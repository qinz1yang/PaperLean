/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Init.System.IO
import Init.System.Platform

public section

/-!
Speculative elaboration by `lean` on the command line, with a fallback.

Some elaboration is done speculatively and checked: with `PAPERLEAN_REUSE_ORACLE`, each reuse of
section variables (`Lean.PaperLean.SectionVars`) is compared in the background with Lean's own
elaboration. If a check fails, `lean` runs again from the start with speculation off
(`PAPERLEAN_EXACT=1`), so that the module's results and messages are then those of Lean's own
elaboration; the messages of a run that speculates are therefore held back until every check has
passed. The run again repeats the side effects of the first, e.g. of `#eval`.
-/

namespace Lean.PaperLean.Speculation

private builtin_initialize enabledRef : IO.Ref Bool ← IO.mkRef false
private builtin_initialize failureRef : IO.Ref (Option String) ← IO.mkRef none
private builtin_initialize checksRef : IO.Ref (Array (Task Unit)) ← IO.mkRef #[]

/-- Whether this process speculates. -/
def isEnabled : BaseIO Bool :=
  enabledRef.get

/-- Turns speculation on for this process if a speculative feature is on (for now only the oracle of
`Lean.PaperLean.SectionVars`, `PAPERLEAN_REUSE_ORACLE`), unless this is the run after a failed check
(`PAPERLEAN_EXACT`) or the platform cannot run `lean` again (Windows). Returns whether it is on. -/
def enable : BaseIO Bool := do
  if System.Platform.isWindows || (← IO.getEnv "PAPERLEAN_EXACT").isSome ||
      (← IO.getEnv "PAPERLEAN_REUSE_ORACLE").isNone then
    return false
  enabledRef.set true
  return true

/-- Records that a speculation differs from Lean's elaboration; `finish` then reports it. -/
def fail (reason : String) : BaseIO Unit :=
  failureRef.modify fun r? => r? <|> some reason

/-- Adds a background check, which `finish` waits for. -/
def addCheck (t : Task Unit) : BaseIO Unit :=
  checksRef.modify (·.push t)

/-- Waits for every check, also those added meanwhile, and returns the first failure, if any. -/
partial def finish : BaseIO (Option String) := do
  let checks ← checksRef.modifyGet fun cs => (cs, #[])
  if checks.isEmpty then
    return (← failureRef.get)
  for t in checks do
    discard <| IO.wait t
  finish

/-- Replaces this process by a run of `lean` with the same arguments and reuse off. Returns only if
that is not possible. -/
@[extern "lean_paperlean_reexec_exact"]
opaque reexecExact : BaseIO Bool

/--
Runs `act`, the elaboration and reporting of the module `fileName` by `lean`. With reuse on, its
standard output is held back until the checks have passed; if one fails, `lean` runs again without
reuse (and with `PAPERLEAN_REUSE_LOG` set, appends the file and the reason to that file).
-/
def withChecks (enabled : Bool) (fileName : String) (act : IO α) : IO α := do
  unless enabled do
    return (← act)
  let buf ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let out ← IO.setStdout (.ofBuffer buf)
  let a ← try act finally discard <| IO.setStdout out
  if let some reason ← finish then
    if (← IO.getEnv "PAPERLEAN_DEBUG_REUSE").isSome then
      IO.eprintln ("PaperLean: running again without reuse: " ++ reason)
    -- (to count the runs again of a build)
    if let some log ← IO.getEnv "PAPERLEAN_REUSE_LOG" then
      IO.FS.withFile log .append (·.putStrLn (fileName ++ ": " ++ reason))
    if !(← reexecExact) then
      throw <| .userError ("PaperLean: could not run again without reuse (" ++ reason ++ ")")
  out.write (← buf.get).data
  out.flush
  return a

end Lean.PaperLean.Speculation
