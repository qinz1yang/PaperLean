# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
# Existing FIFO/symlink nodes must select ordinary setup without following them.
case "$(uname -s)" in MINGW*|MSYS*|CYGWIN*|Windows_NT) return 0 ;; esac
command -v mkfifo >/dev/null || return 0
cd "$TMP_DIR"
export LAKE_ARTIFACT_CACHE=false
cat > lakefile.lean <<'END'
import Lake
open Lean Lake System
open Lake DSL
open Lean.PaperLean.SetupIndex (encodeLinked linkedFileName)
package collision
@[default_target] lean_lib Bench

script runCollision (args) do
  let [mode] := args | error "expected collision mode"
  let ws ← getWorkspace
  let some initial := ws.findModule? `Bench.Early | error "missing first module"
  let some later := ws.findModule? `Bench.Late | error "missing later module"
  discard <| ws.runBuild do
    discard <| (← initial.leanArts.fetch).await
    let dirs ← (ws.dir / ".lake" / "paperlean-setup").readDir
    let some dir := dirs[0]? | error "no run directory"
    let input ← (← later.input.fetch).await
    let bytes := encodeLinked {
      name := later.name, root := later.pkg.leanLibDir.toString, isModule := input.header.isModule
      imports := input.imports.map fun imp => {
        module := imp.module, «target» := none, importAll := imp.importAll
        isExported := imp.isExported, isMeta := imp.isMeta } }
    let file := dir.path / linkedFileName bytes.hash
    if mode == "fifo" then
      discard <| IO.Process.run {cmd := "mkfifo", args := #[file.toString]}
    else
      let other := dir.path / "matching-bytes"
      IO.FS.writeBinFile other bytes
      discard <| IO.Process.run {cmd := "ln", args := #["-s", other.toString, file.toString]}
    try
      discard <| (← later.leanArts.fetch).await
      let side := later.irPath "setup.paperlean"
      let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile side)
      let raw ← IO.ofExcept <| Lean.PaperLean.setupFromJsonCompact? json
      if raw.importArts.contains .anonymous then error "special file used as an indexed setup"
      let actual ← Lean.ModuleSetup.load side
      let stock ← (← later.setup.fetch).await
      unless toJson actual.importArts == toJson stock.importArts do error "fallback differs from Lake"
    finally IO.FS.removeFile file
    return Job.pure ()
  return 0

script fifoSource do
  let ws ← getWorkspace
  let some root := ws.findModule? `Bench | error "no root"
  let some early := ws.findModule? `Bench.Early | error "no early"
  let some late := ws.findModule? `Bench.Late | error "no late"
  discard <| ws.runBuild do
    discard <| (← root.input.fetch).await
    discard <| (← early.leanArts.fetch).await
    IO.FS.removeFile late.leanFile
    IO.FS.writeFile late.leanFile "module\n@[expose] public def ready := 17\n"
    discard <| (← root.leanArts.fetch).await
    let actual ← Lean.ModuleSetup.load (root.irPath "setup.paperlean")
    let stock ← (← root.setup.fetch).await
    unless toJson actual.importArts == toJson stock.importArts do error "wrong generated import"
    return Job.pure ()
  return 0
END
mkdir -p Bench
printf 'module\n' > Bench/Early.lean
printf 'module\n' > Bench/Late.lean
for mode in fifo symlink; do
  rm -rf .lake/build
  run env PAPERLEAN_ACCELERATE=1 python3 - "$mode" <<'PYTHON'
import subprocess
import sys
subprocess.run(['lake', 'run', 'runCollision', sys.argv[1]], timeout=45, check=True)
PYTHON
done

# A preliminary layout reaches Late from Bench while its path is still a FIFO.
# Only the later real Lake input sees the generated regular source.
rm -rf .lake/build
rm -f Bench/Late.lean
mkfifo Bench/Late.lean
printf '%s\n' module 'public import Bench.Early' 'public import Bench.Late' 'example : ready = 17 := rfl' > Bench.lean
run env PAPERLEAN_ACCELERATE=1 python3 - <<'PYTHON'
import subprocess
subprocess.run(['lake', 'run', 'fifoSource'], timeout=45, check=True)
PYTHON
