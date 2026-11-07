/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Lean.PaperLean.OLeanPack
open System Lean Lean.PaperLean

private def checkImports (root first second : FilePath) (kind : String) (n : Nat) : IO Unit := do
  initSearchPath (← findSysroot)
  for i in [:n] do
    if i > 0 then
      if kind == "dir" then
        IO.FS.rename root (root.addExtension "old")
        IO.FS.createDirAll root
      IO.FS.writeBinFile (root / "new") (← IO.FS.readBinFile (if i%2 == 0 then first else second))
      IO.FS.rename (root / "new") (root / "R12.olean")
      if kind == "dir" then IO.FS.removeDirAll (root.addExtension "old")
    let env ← importModules #[{module := `R12}] {}
    unless env.contains (if i%2 == 0 then `R12markerOne else `R12markerTwo) do
      throw (IO.userError s!"wrong import after rebuild {i}")

def main (args : List String) : IO Unit := do
  match args with
  | ["pack", dir, pack] =>
    unless (← OLeanPack.create #[dir] pack) == 1 do throw (IO.userError "initial pack incomplete")
  | ["index", dir, pack] =>
    let (stale, total) ← OLeanPack.staleness pack
    let fs ← OLeanPack.freshFiles #[pack] dir
    IO.println s!"{stale}/{total} {fs.toList}"
  | ["repeat", kind, dir, first, second, n] => checkImports dir first second kind n.toNat!
  | _ => throw (IO.userError "args")
