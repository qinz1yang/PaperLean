/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.Util.Path

/-!
Manifests of native libraries of packages, for `PAPERLEAN_NATIVE_LIBS`
(`src/paperlean/native_libs.cpp`): a library compiled from the `.c` files of modules is used by an
import only for imported modules whose files are those the manifest records.
-/

namespace Lean.PaperLean

/--
Writes to `out` the manifest of the native library `lib`, linked against the libraries of the
manifests `deps` and compiled from `modules`: each module with the `.c` file compiled into `lib` and
the paths of its files, which must be those the `.c` file was generated with, in the order `.olean`,
`.olean.server`, `.olean.private`, `.ir.sig`, `.ir` (empty for a file the module does not have).
-/
@[extern "lean_paperlean_write_native_manifest"]
public opaque writeNativeManifestFiles (out lib : @& String) (deps : @& Array String)
    (modules : @& Array (Name × String × Array String)) : IO Unit

/--
Writes to `out` the manifest of the native library `lib`, linked against the libraries of the
manifests `deps` and compiled from `modules`: each module with the `.c` file compiled into `lib`.
The files of the modules (`.olean`, `.olean.server`, `.olean.private`, `.ir.sig`, `.ir`) are found in
the search path, as importing them finds them, and must be those the `.c` files were generated with.
-/
public def writeNativeManifest (out lib : String) (deps : Array String) (modules : Array (Name × String)) :
    IO Unit := do
  let mods ← modules.mapM fun (m, c) => do
    let olean ← findOLean m
    -- as `OLeanLevel.adjustFileName` and `readIRPartsOfMod` name them
    let files := #[olean, olean.addExtension "server", olean.addExtension "private",
      olean.withExtension "ir.sig", olean.withExtension "ir"]
    return (m, c, ← files.mapM fun f => return if ← f.pathExists then f.toString else "")
  writeNativeManifestFiles out lib deps mods

end Lean.PaperLean
