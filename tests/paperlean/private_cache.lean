import Lake.PaperLean.Cache
import Lean.PaperLean.OLeanPack
open System Lean Lake

def main (args : List String) : IO Unit := do
  let source :: rest := args | throw <| IO.userError "need source"
  let some root ← PaperLean.Cache.root? | throw <| IO.userError "no system cache home"
  let root ← if rest == ["canonical"] then IO.FS.realPath root else pure root
  let cdir := PaperLean.Cache.buildDir root
  PaperLean.Cache.withCacheUse cdir do
    PaperLean.Cache.withKeyLock cdir "pack/private-test" do
      let tmp ← PaperLean.Cache.tempDir cdir "pack/private-test"
      IO.FS.createDirAll tmp
      let n ← Lean.PaperLean.OLeanPack.create #[source] (tmp / "pack.paperlean")
      PaperLean.Cache.publish cdir tmp "pack/private-test"
      IO.println s!"packed {n} source files"
      IO.println (cdir / "pack/private-test/pack.paperlean")
