/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Init.System.IO

/-!
The olean packs written so far during this build (`Lake.PaperLean.BuildData`), for the `lean`
processes that the build starts (`Lake.compileLeanModule`).
-/

namespace Lake.PaperLean.BuildEnv

private builtin_initialize packsRef : IO.Ref (Array String) ← IO.mkRef #[]

/-- Records the pack `pack`, written during this build or for its toolchain. -/
public def addPack (pack : String) : BaseIO Unit :=
  packsRef.modify (·.push pack)

/-- Forgets the packs, at the end of the build. -/
public def clear : BaseIO Unit :=
  packsRef.set #[]

/-- The environment for a `lean` process that the build starts: the packs written so far. -/
public def leanEnv : BaseIO (Array (String × Option String)) := do
  let packs ← packsRef.get
  if packs.isEmpty then return #[]
  return #[("LEAN_OLEAN_PACK", some (String.intercalate ":" packs.toList))]

end Lake.PaperLean.BuildEnv
