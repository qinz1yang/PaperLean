/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Init.System.IO
import Init.Data.Array.BinSearch
import Init.Data.Array.QSort.Basic
import Init.Data.String.TakeDrop

/-!
Olean packs: single files holding the `.olean` and IR files of many modules, from which a process
reads them with one mapping (`LEAN_OLEAN_PACK`) and imports packed modules from tables in the pack.
-/

namespace Lean.PaperLean.OLeanPack

@[extern "lean_paperlean_olean_pack_write"]
private opaque writeCore (chains : @& Array (Array String)) (roots storedRoots : @& Array String)
    (out : @& String) (baseAddr : USize) : IO Nat

/--
Writes the compacted-region files below `roots` (`.olean`, `.olean.server`, `.olean.private`,
`.ir.sig` and `.ir`) into the single file `out`, returning the number of files packed. By
convention, `out` has the suffix `.paperlean`, which marks optional files derived from `.olean`
files.

Setting `LEAN_OLEAN_PACK` to the pack (or to a `:`-separated list of packs) makes Lean map it once
per process and read these files from it, except for those that changed since packing: those, and
the other parts of the same module, are read from disk. A pack written by a different version or
build, whose header or index is damaged, or that was written to since it was written (its writer
records the file's modification time; `verify` also reads its regions), is ignored with a warning. Paths are compared as
strings, so `roots` must be spelled as in the paths Lean reads (e.g. as in `LEAN_PATH`). `baseAddr`
is the address the pack is mapped at; regions of files that are not in the pack and would overlap it
are relocated. `storedRoots`, if given, is how the pack records `roots`: a root recorded as
`^N/rest` is the directory of the pack with `N` trailing components dropped, followed by `/rest`, so
that a pack inside a project keeps working when the project moves. Only the files for which `keep`
holds are packed.
-/
public def create (roots : Array System.FilePath) (out : System.FilePath)
    (baseAddr : USize := 0x200000000000) (storedRoots : Array String := #[])
    (keep : String → IO Bool := fun _ => pure true) : IO Nat := do
  let roots : Array String := roots.map fun r => (r.toString.dropEndWhile (· == '/')).toString
  let exts := #[".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir"]
  let mut found : Array String := #[]
  for root in roots do
    for p in ← System.FilePath.walkDir ⟨root⟩ do
      if exts.any (p.toString.endsWith ·) && (← keep p.toString) then
        found := found.push p.toString
  let files := found.qsort (· < ·)
  let has (f : String) := files.binSearchContains f (· < ·)
  let mut chains : Array (Array String) := #[]
  for f in files do
    if f.endsWith ".olean" then
      let mut chain := #[f]
      if has (f ++ ".server") then
        chain := chain.push (f ++ ".server")
        if has (f ++ ".private") then
          chain := chain.push (f ++ ".private")
      chains := chains.push chain
    else if f.endsWith ".ir.sig" then
      let ir := (f.dropEnd 4).toString  -- without `.sig`
      chains := chains.push (if has ir then #[f, ir] else #[f])
  writeCore chains roots storedRoots out.toString baseAddr

/--
Writes the pack `out`, mapped at `baseAddr`, holding the files `chains` (each the files of a module
part read together, e.g. `#[a.olean, a.olean.server, a.olean.private]` or `#[a.ir.sig, a.ir]`, by
absolute path) below the directories `roots`, which the pack records as they are. Returns the
number of files packed. See `create`.
-/
public def createOf (chains : Array (Array String)) (roots : Array String) (out : System.FilePath)
    (baseAddr : USize) : IO Nat :=
  writeCore chains roots #[] out.toString baseAddr

@[extern "lean_paperlean_pack_fresh_files"]
private opaque freshFilesCore (packs : @& Array String) (root : @& String) : IO (Array String)

/--
The files below `root` (relative to it) that Lean reads from the packs `packs` if `LEAN_OLEAN_PACK`
lists them in this order: a file is read from the first pack that has it below a root that is a
prefix of its path, unless a file of its module changed since packing. A pack that cannot be read
serves nothing. Only the packs' indexes are read.
-/
public def freshFiles (packs : Array System.FilePath) (root : System.FilePath) : IO (Array String) :=
  freshFilesCore (packs.map (·.toString)) (root.toString.dropEndWhile (· == '/')).toString

/--
Returns the number of files read by this process from olean packs, and the number of files below
the roots of a pack that were read from disk instead.
-/
@[extern "lean_paperlean_olean_pack_stats"]
public opaque stats : BaseIO (Nat × Nat)

/-- The number of modules of the pack `pack` whose files changed since packing (they are read from
disk), and the number of its modules. Reads only the pack's index. -/
@[extern "lean_paperlean_pack_staleness"]
public opaque staleness (pack : @& String) : IO (Nat × Nat)

/-- Why the pack `pack` cannot be used, or `""` if it can and its regions are as they were written,
which reads all of it. (Lean compares only the pack's modification time with the one its writer
recorded: reading the regions on every use would take too long.) -/
@[extern "lean_paperlean_olean_pack_verify"]
public opaque verify (pack : @& String) : IO String

end Lean.PaperLean.OLeanPack
