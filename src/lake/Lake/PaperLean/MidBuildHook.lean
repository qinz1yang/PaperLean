/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lake.Build.Context
public import Lake.Config.Workspace
public import Lake.PaperLean.Schedule

/-!
The calls of upstream Lake modules (`Lake.Build.Run`, `Lake.Build.Module`) into the mid-build
preparation (`Lake.PaperLean.MidBuild`). They go through here, filled by the `paperlean` front end
(`Lake.PaperLean.Cli`, `MidBuild.install`) before it builds, because importing `MidBuild` itself
from those modules would add what it imports (`Prepare`, `Native`, ...) to what `import Lake` brings,
which must stay official Lean's (`tests/paperlean/env_additions.sh`). This module imports only what
those modules import already. Under plain `lake`, nothing fills it and every call does nothing.
-/

namespace Lake.PaperLean.MidBuildHook

/-- The mid-build preparation's entry points (`Lake.PaperLean.MidBuild`). -/
public structure Hooks where
  start : BuildContext → Workspace → Schedule.Session → Bool → BaseIO Unit
  compileStarting : BuildContext → Module → IO Unit
  moduleDone : BuildContext → Module → IO Unit
  compileAborted : BuildContext → Module → IO Unit
  finish : BuildContext → BaseIO Unit

private initialize hooks : IO.Ref (Option Hooks) ← IO.mkRef none

/-- Installs the entry points (the `paperlean` front end, once, before it builds). -/
public def install (h : Hooks) : BaseIO Unit :=
  hooks.set (some h)

public def start (ctx : BuildContext) (ws : Workspace) (scheduler : Schedule.Session) (enable : Bool) :
    BaseIO Unit := do
  if let some h ← hooks.get then h.start ctx ws scheduler enable

public def compileStarting (ctx : BuildContext) (mod : Module) : IO Unit := do
  if let some h ← hooks.get then h.compileStarting ctx mod

public def moduleDone (ctx : BuildContext) (mod : Module) : IO Unit := do
  if let some h ← hooks.get then h.moduleDone ctx mod

public def compileAborted (ctx : BuildContext) (mod : Module) : IO Unit := do
  if let some h ← hooks.get then h.compileAborted ctx mod

public def finish (ctx : BuildContext) : BaseIO Unit := do
  if let some h ← hooks.get then h.finish ctx

end Lake.PaperLean.MidBuildHook
