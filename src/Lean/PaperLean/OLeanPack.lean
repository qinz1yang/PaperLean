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
A pack of the shared cache (`Lake.PaperLean.Cache`) is read through a binding of each workspace that
uses it (`bind`), which `LEAN_OLEAN_PACK` lists in its place.
-/

namespace Lean.PaperLean.OLeanPack

@[extern "lean_paperlean_olean_pack_write"]
private opaque writeCore (chains : @& Array (Array String)) (roots storedRoots : @& Array String)
    (out : @& String) (baseAddr : USize) (sync bound : Bool) : IO Nat

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
With `bound`, the pack is read only through bindings (`bind`), which give its roots.
-/
public def create (roots : Array System.FilePath) (out : System.FilePath)
    (baseAddr : USize := 0x200000000000) (storedRoots : Array String := #[])
    (keep : String → IO Bool := fun _ => pure true) (sync := true) (bound := false) : IO Nat := do
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
  writeCore chains roots storedRoots out.toString baseAddr sync bound

/--
Writes the pack `out`, mapped at `baseAddr`, holding the files `chains` (each the files of a module
part read together, e.g. `#[a.olean, a.olean.server, a.olean.private]` or `#[a.ir.sig, a.ir]`, by
absolute path) below the directories `roots`, which the pack records as they are. Returns the
number of files packed. See `create`.
-/
public def createOf (chains : Array (Array String)) (roots : Array String) (out : System.FilePath)
    (baseAddr : USize) (sync := true) : IO Nat :=
  writeCore chains roots #[] out.toString baseAddr sync false

@[extern "lean_paperlean_pack_fresh_files"]
private opaque freshFilesCore (packs : @& Array String) (root : @& String) : IO (Array String)

/--
The files below `root` (relative to it) that Lean reads from the packs `packs` (or bindings) if
`LEAN_OLEAN_PACK` lists them in this order: a file is read from the first pack that has it below a
root that is a prefix of its path, unless a file of its module changed since packing (or binding). A
pack that cannot be read serves nothing. Only the packs' indexes are read.
-/
public def freshFiles (packs : Array System.FilePath) (root : System.FilePath) : IO (Array String) :=
  freshFilesCore (packs.map (·.toString)) (root.toString.dropEndWhile (· == '/')).toString

/--
Returns the number of files read by this process from olean packs, and the number of files below
the roots of a pack that were read from disk instead.
-/
@[extern "lean_paperlean_olean_pack_stats"]
public opaque stats : BaseIO (Nat × Nat)

/-- The number of modules of the pack (or binding) `pack` whose files changed since packing (or binding;
they are read from disk), and the number of its modules. Reads only the pack's index. -/
@[extern "lean_paperlean_pack_staleness"]
public opaque staleness (pack : @& String) : IO (Nat × Nat)

/-- Has this process read its own imports from the packs `packs` (`:`-separated) and the import image
`image` (`""`: none) if `LEAN_OLEAN_PACK` is not set at its first import, saying nothing about them.
Only the first call before that import counts; no other process inherits it. -/
@[extern "lean_paperlean_use_process_packs"]
public opaque useForProcess (packs image : @& String) : BaseIO Unit

/-- Why the pack `pack` (or the pack that the binding `pack` binds) cannot be used, or `""` if it can
and its index and regions are as they were written, which reads all of it. (Lean compares the pack's identity with the one recorded after it was
written, and checks the parts of the index that it uses by their checksums, but not the regions:
reading the whole pack on every use would take too long.) -/
@[extern "lean_paperlean_olean_pack_verify"]
public opaque verify (pack : @& String) : IO String

/-- The file next to the pack `pack` that records the pack's identity, which goes with the pack. -/
@[extern "lean_paperlean_pack_identity_file"]
public opaque identityFile (pack : @& String) : String

/-- Why Lean ignores the pack or binding `pack` as a whole, or `""` if it does not: what it finds in
the binding, and in the pack's header and identity, the small part of a pack that it reads before it
maps it. -/
@[extern "lean_paperlean_pack_why_ignored"]
public opaque whyIgnored (pack : @& String) : BaseIO String

/-- Why the import image `image` (`Lean.PaperLean.writeImportImage`) cannot be used, or `""` if it can
and its tables are as they were written, which reads all of it (but not whether it belongs to the
pack in use). Lean compares the image's modification time with the one its writer recorded, and
checks the parts of the tables that it uses by their checksums. -/
@[extern "lean_paperlean_import_image_verify"]
public opaque verifyImportImage (image : @& String) : IO String

/-- The pack content hash of these exact bytes, or the empty string on unsupported platforms. -/
@[extern "lean_paperlean_hash_bytes"]
public opaque hashBytes (bytes : @& ByteArray) : String

/-- Read the exact bytes of a stable regular file with the given identity. A nonempty `hash` must
also match its pack digest. Opening a special file substituted for `path` cannot block the reader. -/
@[extern "lean_paperlean_read_verified_bytes"]
public opaque readVerifiedBytes (path : @& String) (identity : @& ByteArray) (hash : @& String) : IO ByteArray

/-- The identity of the final directory entry itself if it is a regular file. -/
@[extern "lean_paperlean_owned_file_identity"]
public opaque ownedFileIdentity (path : @& String) : BaseIO (Option ByteArray)

/-- Read a verified owned cache file, rejecting a final symlink even if its target has the expected identity. -/
@[extern "lean_paperlean_read_verified_owned_bytes"]
public opaque readVerifiedOwnedBytes (path : @& String) (identity : @& ByteArray) (hash : @& String) : IO ByteArray

@[extern "lean_paperlean_hash_files"]
private opaque hashFilesCore (files scope : @& Array String) (record : @& String) (jobs : USize) :
    IO (Array (ByteArray × String))

/--
The identities (as `fileIdentity`) and content hashes (as packs know files by them) of the regular
files `files`, both empty for one that cannot be read or that changed while it was read, hashed on
`jobs` threads. The record `record` (a side file) keeps what was found, so that a file that has the
same identity later is not read again: afterwards it holds what was found of `files`, and keeps what
it held of the other files, except those below the directories `scope`.
-/
public def hashFiles (files : Array String) (scope : Array System.FilePath) (record : System.FilePath)
    (jobs : Nat) : IO (Array (ByteArray × String)) :=
  hashFilesCore files (scope.map fun d => (d.toString.dropEndWhile (· == '/')).toString) record.toString
    jobs.toUSize

/--
Writes to `out` the binding of the pack `pack` (`create` with `bound`) to the roots `roots`, which it
records as `storedRoots` (as `create` does), unless `out` holds it already: a packed file is bound to
the file at its path below its root if the record `record` (`hashFiles`) has its content hash for that
file, which still has the identity that the record has; Lean reads the others from disk. Returns the
number of the pack's files that are bound, and of all of them.
-/
@[extern "lean_paperlean_pack_bind"]
public opaque bind (pack : @& String) (roots storedRoots : @& Array String) (record out : @& String) :
    IO (Nat × Nat)

/-- Open a stable regular file for locking. Symlinks to regular files are accepted. Absent,
replaced and special files return `none`; opening a raced special file cannot block. -/
@[extern "lean_paperlean_open_regular_for_lock"]
public opaque openRegularForLock (path : @& String) : IO (Option IO.FS.Handle)

end Lean.PaperLean.OLeanPack
