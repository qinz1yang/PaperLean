/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake.PaperLean.BuildData
open System Lean.PaperLean
def main (args : List String) : IO Unit := do
  match args with
  | ["cache", cache, root] =>
    IO.println ((← Lake.PaperLean.BuildData.toolchainPack cache root false).getD "none")
  | ["pack", root, file] => IO.println (← OLeanPack.create #[root] file)
  | ["verify", file] =>
    unless (← OLeanPack.verify file).isEmpty do throw (IO.userError "invalid pack")
  | _ => throw (IO.userError "args")
