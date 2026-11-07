/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.PaperLean.OLeanPack

open Lean.PaperLean System

private def awaitGate (p : FilePath) : IO Unit := do
  for _ in [0:2000] do
    if ← p.pathExists then return
    IO.sleep 10
  throw <| IO.userError s!"timed out waiting for {p}"

private def require (ok : Bool) (msg : String) : IO Unit :=
  unless ok do throw <| IO.userError msg

private def verifyPack (pack : FilePath) : IO Unit := do
  let why ← OLeanPack.verify pack.toString
  require why.isEmpty s!"invalid pack: {why}"

def main (args : List String) : IO Unit := do
  let [dir] := args | throw <| IO.userError "expected fixture directory"
  let dir : FilePath := dir
  let root := dir / "inputs"
  let a := (root / "A.olean").toString
  let b := (root / "B.olean").toString
  let hashes := dir / "hashes"
  let pack := dir / "out.paperlean"
  let binding := dir / "binding"
  awaitGate (dir / "start")
  let h := fun (file : String) => do
    let rows ← OLeanPack.hashFiles #[file] #[root] hashes 1
    let some (_, digest) := rows[0]? | throw <| IO.userError "missing hash"
    require (digest == OLeanPack.hashBytes (← IO.FS.readBinFile file)) "hash mismatch"
  let tasks ← #[a,b,a,b].mapM fun f => IO.asTask (h f) .dedicated
  for t in tasks do IO.ofExcept (← IO.wait t)
  let hashes' ← OLeanPack.hashFiles #[a,b] #[root] hashes 2
  require (hashes'.size == 2) "missing hash rows"
  require ((← OLeanPack.hashFiles #[] #[] (dir / "empty") 1).isEmpty) "invalid empty record"
  let mk := fun (file : String) (base : USize) =>
    OLeanPack.createOf #[#[file]] #[root.toString] pack base
  let first ← mk a 0x200000000000
  require (first == 1) "initial pack has no region"
  verifyPack pack
  let (bound, total) ← OLeanPack.bind pack.toString #[root.toString] #[] hashes.toString binding.toString
  require (bound == 1 && total == 1) "binding did not read the published hash record"
  IO.FS.writeFile (dir / "ready") ""
  awaitGate (dir / "writers")
  let ta ← IO.asTask (mk a 0x200000000000) .dedicated
  let tb ← IO.asTask (mk b 0x240000000000) .dedicated
  let na ← IO.ofExcept (← IO.wait ta)
  let nb ← IO.ofExcept (← IO.wait tb)
  require (na == 1 && nb == 1) "concurrent writers dropped a region"
  verifyPack pack
  let errorDir := dir / "occupied"
  let ok ← (OLeanPack.hashFiles #[a] #[] errorDir 1).toBaseIO
  require (ok matches .error _) "renaming over a directory unexpectedly succeeded"
  IO.println "pack, binding and hash publications passed"
