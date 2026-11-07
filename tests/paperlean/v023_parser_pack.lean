/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Lean.PaperLean.OLeanPack
open Lean Parser
abbrev Row := Array (ScopedEnvExtension.Entry ParserExtension.OLeanEntry)
@[extern "lean_paperlean_parser_row_density"]
opaque lookupHint (data : @& ModuleData) (row : @& Row) : UInt8
@[extern "lean_paperlean_pack_module_find"]
opaque findPack (n : @& Name) : UInt32
@[extern "lean_paperlean_pack_module_parts"]
opaque parts (m : UInt32) (ir : Bool) (n : UInt32) (root : @& Option String) :
  BaseIO (Option (Array (ModuleData × CompactedRegion)))
@[extern "lean_paperlean_pack_join"]
opaque joinChecked (wait : Bool) : BaseIO Bool
unsafe def md (entries : Array (Name × Row)) : ModuleData :=
  { isModule := false, imports := #[], constNames := #[], constants := #[], extraConstNames := #[],
    entries := unsafeCast entries }
def mkRow (dense : Bool) (n : Nat := 8192) : Row :=
  (Array.range n).map fun i => .global (.token (if dense then "one" else toString i))
unsafe def generate (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  let loose := dir.withFileName "loose"
  IO.FS.createDirAll loose
  let missing := ScopedEnvExtension.Entry.global (ParserExtension.OLeanEntry.parser `MissingCategory `MissingParser 100)
  let looseRow : Row := #[.global (.token "a-wrapped-loose"), missing]
  saveModuleData (loose / "LooseBad.olean") `LooseBad (md #[(``Lean.Parser.parserExtension, looseRow)])
  -- Positions 1 and 2 are between density samples.
  let wrapped := ((mkRow true).set! 1 (.global (.token "a-wrapped-packed"))).set! 2 missing
  for (nm, row) in [("Dense",mkRow true),("Sparse",mkRow false),("Small",mkRow true 64),
       ("Wrapped", wrapped),
       ("Malformed",(Array.replicate 8192 (.global (.token "paperlean-parser-hint-fixture")) : Row).set! 0
         (.global (.parser `MissingCategory `MissingParser 100))),
       ("OldWord",(Array.replicate 8192 (.global (.token (String.ofList (List.replicate 4100 'w')))) : Row))] do
    let data := md #[( ``Lean.Parser.parserExtension, row), (`Another, mkRow true 4200)]
    saveModuleData (dir / (nm ++ ".olean")) nm.toName data
def readData (nm : Name) : IO (ModuleData × CompactedRegion) := do
  let some ps ← parts (findPack nm) false 1 none | throw <| IO.userError s!"not packed {nm}"
  let some x := ps[0]? | throw <| IO.userError "empty chain"
  return x
unsafe def extractRow (d : ModuleData) : Row := unsafeCast d.entries[0]!.2
unsafe def main (args : List String) : IO Unit := do
  let dir : System.FilePath := args[1]!
  match args[0]! with
  | "make" => generate dir
  | "pack" =>
    let n ← Lean.PaperLean.OLeanPack.create #[dir] args[2]! (baseAddr := 0x200000000000)
    IO.println s!"packed {n}"
  | mode =>
    let (dense,dreg) ← readData `Dense
    let (sparse,sreg) ← readData `Sparse
    let (small,mreg) ← readData `Small
    let (mal,mareg) ← readData `Malformed
    let (old,wreg) ← readData `OldWord
    unless ← joinChecked true do throw <| IO.userError "changed pack"
    let a := extractRow dense; let b := extractRow sparse
    let values := [lookupHint dense a, lookupHint sparse b, lookupHint small (extractRow small),
      lookupHint sparse a, lookupHint dense b, lookupHint (md #[]) a,
      lookupHint dense (unsafeCast dense.entries[1]!.2), lookupHint dense (mkRow true),
      lookupHint mal (extractRow mal), lookupHint old (extractRow old)]
    IO.println s!"{mode} {values}"
    unless values == (if mode=="new" then [2,1,0,0,0,0,0,0,0,0] else [0,0,0,0,0,0,0,0,0,0]) do
      throw <| IO.userError "unexpected hint results"
    unless dreg.size>0 && sreg.size>0 && mreg.size>0 && mareg.size>0 && wreg.size>0 do throw <| IO.userError "region missing"
