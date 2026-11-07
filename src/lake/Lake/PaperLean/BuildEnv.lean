/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Init.System.IO
import Lake.PaperLean.Env

/-!
What the `lean` processes that a build starts (`Lake.compileLeanModule`) get from PaperLean: the olean
packs written so far during this build (`Lake.PaperLean.BuildData`), and under a `paperlean` command
the request to reuse results (`PAPERLEAN_REUSE`, `Lean.PaperLean.Speculation.reuse`).
-/

namespace Lake.PaperLean.BuildEnv

/-- Packs published to children of a single build. -/
public abbrev PackList := IO.Ref (Array String)

private initialize standalone : IO.Ref PackList ← IO.mkRef (← IO.mkRef #[])

public def standalonePacks : BaseIO PackList := standalone.get

/-- New standalone jobs cannot inherit a retiring session's pack list. -/
public def renewStandalone : BaseIO Unit := do
  standalone.set (← IO.mkRef #[])
private initialize live : IO.Ref (List (PackList × Bool)) ← IO.mkRef []

/-- Register an empty pack list before this run starts any compiler children. -/
public def enter (enabled : Bool) : BaseIO PackList := do
  let packs ← IO.mkRef #[]
  live.modify ((packs, enabled) :: ·)
  return packs

public def leave (packs : PackList) : BaseIO Unit :=
  live.modify fun xs => xs.eraseP fun (p, _) => unsafe ptrEq packs p

/-- Context-free callers use the sole enabled build, or a standalone list outside builds. -/
private def selected? : BaseIO (Option PackList) := do
  match ← live.get with
  | [] => return some (← standalonePacks)
  | [(packs, true)] => return some packs
  | _ => return none

public def addPack (pack : String) : BaseIO Unit := do
  if let some packs ← selected? then packs.modify (·.push pack)

public def clear : BaseIO Unit := do
  if let some packs ← selected? then packs.set #[]

public def makeEnv (packs? : Option PackList) : BaseIO (Array (String × Option String)) := do
  let env := if (← accelerated) then #[("PAPERLEAN_REUSE", some "1")] else #[]
  let some packs := packs? | return env
  let paths ← packs.get
  if paths.isEmpty then return env
  return env.push ("LEAN_OLEAN_PACK", some (String.intercalate ":" paths.toList))

/-- Environment for a standalone caller, or for the only active workspace build. -/
public def leanEnv : BaseIO (Array (String × Option String)) := do
  makeEnv (← selected?)

end Lake.PaperLean.BuildEnv
