/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import Lake.PaperLean.BuildSessions
import Lake.PaperLean.Env

namespace Lake.PaperLean.SourceInputScope

-- Run.lean needs only the lifetime of the optional cache. The stock module
-- parser, private cached state and actual reading are confined to SourceInputs.
private inductive Life where
  | initial
  | open (finish : BaseIO Unit)
  | closed

private initialize scopes : BuildSessions (BuildMutex Life) ← BuildSessions.new

public def withRun (ctx : BuildContext) (enabled : Bool) (act : BaseIO α) : BaseIO α := do
  unless enabled && (← accelerated) && (← IO.getEnv "PAPERLEAN_SOURCE_INPUT_CACHE") != some "0" do return ← act
  let scope ← BuildMutex.new Life.initial
  unless ← scopes.insertFresh ctx scope do return ← act
  try act finally
    let finish ← scope.atomically do
      let s ← get
      set Life.closed
      return match s with | .open finish => finish | _ => pure ()
    try finish finally discard <| scopes.take? ctx

-- One lazy initialization per owning build. No data or submission API lives
-- here, and the first action is never replaced by another caller.
def attach (ctx : BuildContext) (init : BaseIO (BaseIO Unit)) : BaseIO Unit := do
  let some scope ← scopes.find? ctx | return
  scope.atomically do
    if (← get) matches .initial then set (Life.open (← init))

end Lake.PaperLean.SourceInputScope
