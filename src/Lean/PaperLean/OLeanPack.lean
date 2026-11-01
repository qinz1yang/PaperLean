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

-- (no `SizeOf` instances for PaperLean's types: an instance of a module of `Lean` would be one of
-- every environment that imports it, which Lean's searches would try)
set_option genSizeOf false
set_option genInjectivity false

/-!
Olean packs: single files holding the `.olean` and IR files of many modules, from which a process
reads them with one mapping (`LEAN_OLEAN_PACK`) and imports packed modules from tables in the pack.
-/

namespace Lean.PaperLean.OLeanPack

@[extern "lean_paperlean_olean_pack_write"]
private opaque writeCore (chains : @& Array (Array String)) (roots storedRoots : @& Array String)
    (out : @& String) (baseAddr : USize) (sync : Bool) : IO Nat

/--
Writes the compacted-region files below `roots` (`.olean`, `.olean.server`, `.olean.private`,
`.ir.sig` and `.ir`) into the single file `out`, returning the number of files packed. By
convention, `out` has the suffix `.paperlean`, which marks optional files derived from `.olean`
files.

Setting `LEAN_OLEAN_PACK` to the pack (or to a `:`-separated list of packs) makes Lean map it once
per process and read these files from it, except for those that changed since packing: those, and
the other parts of the same module, are read from disk. A pack written by a different version or
build, whose header is damaged, or that changed since it was written (the small file
`identityFile out` next to it records the file's device, inode, size and times, compared with one
`stat`, so a copy of a pack is not used either), is ignored with a warning, and so are the damaged
entries of its index, which Lean finds by checksums of the parts of the index that it uses. As for
`.olean` files under official Lean, damage to its regions that leaves the file's metadata alone is
not found on use: only `verify` reads all of it (`paperlean status --verify`). The pack is read-only,
so that tools do not change it in place while it is mapped; it is replaced by renaming. Paths are compared as
strings, so `roots` must be spelled as in the paths Lean reads (e.g. as in `LEAN_PATH`). `baseAddr`
is the address the pack is mapped at; regions of files that are not in the pack and would overlap it
are relocated. `storedRoots`, if given, is how the pack records `roots`: a root recorded as
`^N/rest` is the directory of the pack with `N` trailing components dropped, followed by `/rest`, so
that a pack inside a project keeps working when the project moves. Only the files for which `keep`
holds are packed. With `sync`, the pack is on the disk before it is renamed to `out`, so that a pack
found under its name after a crash of the system is whole; packs deleted after a crash need not be.
-/
public def create (roots : Array System.FilePath) (out : System.FilePath)
    (baseAddr : USize := 0x200000000000) (storedRoots : Array String := #[])
    (keep : String → IO Bool := fun _ => pure true) (sync := true) : IO Nat := do
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
  writeCore chains roots storedRoots out.toString baseAddr sync

/--
Writes the pack `out`, mapped at `baseAddr`, holding the files `chains` (each the files of a module
part read together, e.g. `#[a.olean, a.olean.server, a.olean.private]` or `#[a.ir.sig, a.ir]`, by
absolute path) below the directories `roots`, which the pack records as they are. Returns the
number of files packed. See `create`.
-/
public def createOf (chains : Array (Array String)) (roots : Array String) (out : System.FilePath)
    (baseAddr : USize) (sync := true) : IO Nat :=
  writeCore chains roots #[] out.toString baseAddr sync

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

/-- Why the pack `pack` cannot be used, or `""` if it can and its index and regions are as they were
written, which reads all of it. (Lean compares the pack's identity with the one recorded after it was
written, and checks the parts of the index that it uses by their checksums, but not the regions:
reading the whole pack on every use would take too long.) -/
@[extern "lean_paperlean_olean_pack_verify"]
public opaque verify (pack : @& String) : IO String

/-- The file next to the pack `pack` that records the pack's identity, which goes with the pack. -/
@[extern "lean_paperlean_pack_identity_file"]
public opaque identityFile (pack : @& String) : String

/-- Why Lean ignores the pack `pack` as a whole, or `""` if it does not: what it finds in the pack's
header and identity, the small part of a pack that it reads before it maps it. -/
@[extern "lean_paperlean_pack_why_ignored"]
public opaque whyIgnored (pack : @& String) : BaseIO String

/-- Why the import image `image` (`Lean.PaperLean.writeImportImage`) cannot be used, or `""` if it can
and its tables are as they were written, which reads all of it (but not whether it belongs to the
pack in use). Lean compares the image's modification time with the one its writer recorded, and
checks the parts of the tables that it uses by their checksums. -/
@[extern "lean_paperlean_import_image_verify"]
public opaque verifyImportImage (image : @& String) : IO String

end Lean.PaperLean.OLeanPack
