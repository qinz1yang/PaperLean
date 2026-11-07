/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.PaperLean.OLeanPack
import Lean.PaperLean.ImportState

/-!
Writes an olean pack of the `.olean` and IR files below the given roots, to be used with
`LEAN_OLEAN_PACK` (`Lean.PaperLean.OLeanPack.create`), or, with `--image`, an import image of the
pack in `LEAN_OLEAN_PACK` for `LEAN_IMPORT_IMAGE`, after importing the given modules, which registers
the simp sets they define (`Lean.PaperLean.writeImportImage`).

usage: lean --run paperlean/Pack.lean [--base <hex address>] <out.paperlean> <root>...
       lean --run paperlean/Pack.lean --image <out.paperlean> <module>...

Roots must be spelled exactly as in the paths Lean reads (the entries of `LEAN_PATH`, the toolchain's
`lib/lean`). Packs used together need disjoint address ranges.
-/

open Lean

private def parseBase? (s : String) : Option USize := do
  let digits := match s.toList with
    | '0' :: 'x' :: ds | '0' :: 'X' :: ds => ds
    | ds => ds
  guard (!digits.isEmpty)
  let n ← digits.foldlM (init := 0) fun n c => do
    let x := c.toLower
    let digit ← if c.isDigit then some (c.toNat - '0'.toNat)
      else if 'a' ≤ x && x ≤ 'f' then some (x.toNat - 'a'.toNat + 10) else none
    let n := n * 16 + digit
    guard (n < USize.size)
    return n
  return n.toUSize

def usage : IO UInt32 := do
  IO.eprintln "usage: lean --run paperlean/Pack.lean [--base <hex address>] <out.paperlean> <root>..."
  IO.eprintln "       lean --run paperlean/Pack.lean --image <out.paperlean> <module>..."
  return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | "--image" :: out :: mods =>
    initSearchPath (← findSysroot (lean := (← IO.appPath).toString))
    unsafe enableInitializersExecution
    let _env ← importModules (mods.map fun m => { module := m.toName }).toArray {} (loadExts := true)
    let n ← PaperLean.writeImportImage out
    IO.println s!"wrote an import image of {n} entries to {out}"
    return 0
  | _ =>
    let some (base, args) := (match args with
      | "--base" :: b :: rest => (parseBase? b).map (·, rest)
      | ["--base"] => none
      | _ => some (0x200000000000, args)) | usage
    let out :: roots := args | usage
    let n ← PaperLean.OLeanPack.create (roots.map System.FilePath.mk).toArray out base
    IO.println s!"packed {n} files into {out}"
    return 0
