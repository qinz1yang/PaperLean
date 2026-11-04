import Lean
/-!
Regression tests for imported constant precedence, ownership, visibility and parallel assembly. The
module data is written to `_tmp_importConstants` in the working directory. Run by
`import_regressions.sh`.
-/

open Lean System

namespace ImportConstantsProbe

private def ax (name : Name) (type : Expr := .sort .zero) (isUnsafe := false) : ConstantInfo :=
  .axiomInfo { name, levelParams := [], type, isUnsafe }

private def theoremInfo (name witness : Name) : ConstantInfo :=
  .thmInfo { name, levelParams := [], type := .const `Fixture.P [], value := .const witness [] }

private def definitionInfo (name : Name) : ConstantInfo :=
  .defnInfo {
    name := name
    levelParams := []
    type := .sort (.succ .zero)
    value := .sort .zero
    hints := .opaque
    safety := .safe }

private def data (isModule : Bool) (constants : Array ConstantInfo)
    (extraConstNames : Array Name := #[]) : ModuleData := {
  isModule, imports := #[], constants, constNames := constants.map (·.name),
  extraConstNames, entries := #[]
}

private def saveLegacy (dir : FilePath) (name : Name) (contents : ModuleData) : IO ImportArtifacts := do
  let file := modToFilePath dir name "olean"
  IO.FS.createDirAll file.parent.get!
  saveModuleDataParts name #[(file, contents)]
  return .ofArrays #[#[file], #[]]

private def saveModern (dir : FilePath) (name : Name) (exported privateData : ModuleData)
    : IO ImportArtifacts := do
  let file := modToFilePath dir name "olean"
  IO.FS.createDirAll file.parent.get!
  let server := file.withExtension "olean.server"
  let priv := file.withExtension "olean.private"
  let sig := file.withExtension "ir.sig"
  let ir := file.withExtension "ir"
  saveModuleDataParts name #[(file, exported), (server, exported), (priv, privateData)]
  saveModuleDataParts name #[(sig, exported), (ir, privateData)]
  return .ofArrays #[#[file, server, priv], #[sig, ir]]

private def options (parallel : Bool) : Options :=
  ({} : Options).setBool `importModules.parallelConstants parallel

private def load (imports : Array Import) (arts : NameMap ImportArtifacts) (level : OLeanLevel)
    (parallel : Bool) (leakEnv := false) : IO Environment :=
  importModules imports (options parallel) (level := level) (arts := arts)
    (loadExts := false) (leakEnv := leakEnv)

private structure Snapshot where
  privateEntries : Array (Name × ConstantInfo)
  privateBuckets : Nat
  ownerEntries : Array (Name × ModuleIdx)
  ownerBuckets : Nat
  publicLookups : Array (Option ConstantInfo)
  moduleNames : Array Name
  regions : Nat
  deriving BEq

private def snapshot (env : Environment) (keys : Array Name) : Snapshot := {
  privateEntries := env.constants.map₁.toArray
  privateBuckets := env.constants.numBuckets
  ownerEntries := env.const2ModIdx.toArray
  ownerBuckets := Std.HashMap.Internal.numBuckets env.const2ModIdx
  publicLookups := keys.map ((env.setExporting true).find? ·)
  moduleNames := env.header.moduleNames
  regions := env.header.regions.size
}

private def checkPair (label : String) (imports : Array Import) (arts : NameMap ImportArtifacts)
    (level : OLeanLevel) (keys : Array Name) (check : Environment → IO Unit)
    (leakEnv := false) : IO Unit := do
  let sequential ← load imports arts level false leakEnv
  let parallel ← load imports arts level true leakEnv
  unless snapshot sequential keys == snapshot parallel keys do
    throw <| IO.userError s!"{label}: table contents/order/capacity or environment header differ"
  check sequential
  check parallel
  IO.println s!"ok: {label}"

private def checkValue (env : Environment) (name : Name) (value : Option ConstantInfo)
    (exported := false) : IO Unit := do
  unless (env.setExporting exported).find? name == value do
    throw <| IO.userError s!"unexpected constant {name}, exported={exported}"

private def checkOwner (env : Environment) (name : Name) (idx : Nat) : IO Unit := do
  unless env.const2ModIdx[name]? == some idx do
    throw <| IO.userError s!"unexpected owner for {name}"

private def errorText (act : IO Environment) : IO String := do
  try
    let _ ← act
    return "unexpected success"
  catch e => return e.toString

private def checkError (label : String) (imports : Array Import)
    (arts : NameMap ImportArtifacts) (expected : String) : IO Unit := do
  let sequential ← errorText (load imports arts .private false)
  let parallel ← errorText (load imports arts .private true)
  unless sequential == expected && parallel == sequential do
    throw <| IO.userError s!"{label}: error mismatch\nsequential={sequential}\nparallel={parallel}\nexpected={expected}"
  IO.println s!"ok: {label}"

private def test (dir : FilePath) : IO Unit := do
  let p := ax `Fixture.P
  let w1 := ax `Fixture.w1 (.const `Fixture.P [])
  let w2 := ax `Fixture.w2 (.const `Fixture.P [])
  let qa := ax `Fixture.q (.const `Fixture.P [])
  let qt1 := theoremInfo `Fixture.q `Fixture.w1
  let qt2 := theoremInfo `Fixture.q `Fixture.w2
  let hidden := ax `Fixture.hidden
  let unique := ax `Fixture.unique
  let qdef := definitionInfo `Fixture.duplicate
  let first := `ConstProbe.First
  let second := `ConstProbe.Second
  let third := `ConstProbe.Third
  let weak := `ConstProbe.Weak
  let extra := `ConstProbe.Extra
  let conflict := `ConstProbe.Conflict
  let later := `ConstProbe.Later
  let modernA := `ConstProbe.ModernA
  let modernB := `ConstProbe.ModernB
  let modernUnique := `ConstProbe.ModernUnique
  let modernRich := `ConstProbe.ModernRich
  let mut arts : NameMap ImportArtifacts := {}
  arts := arts.insert first (← saveLegacy dir first (data false #[p,w1,w2,qa] #[`Fixture.extra]))
  arts := arts.insert second (← saveLegacy dir second (data false #[qt1] #[`Fixture.extra,`Fixture.q]))
  arts := arts.insert third (← saveLegacy dir third (data false #[qt2,unique] #[`Fixture.laterExtra]))
  arts := arts.insert weak (← saveLegacy dir weak (data false #[qa]))
  arts := arts.insert extra (← saveLegacy dir extra (data false #[] #[`Fixture.duplicate]))
  arts := arts.insert conflict (← saveLegacy dir conflict (data false #[qdef]))
  arts := arts.insert later (← saveLegacy dir later (data false #[] #[`Fixture.duplicate]))
  let conflict2 := `ConstProbe.Conflict2
  arts := arts.insert conflict2 (← saveLegacy dir conflict2 (data false #[qdef]))
  arts := arts.insert modernA (← saveModern dir modernA
    (data true #[p,w1,w2,qa]) (data true #[p,w1,w2,qt1,hidden] #[`Fixture.extra]))
  arts := arts.insert modernB (← saveModern dir modernB (data true #[qa]) (data true #[qt2]))
  arts := arts.insert modernUnique (← saveModern dir modernUnique (data true #[unique]) (data true #[unique]))
  arts := arts.insert modernRich (← saveModern dir modernRich (data true #[qt2]) (data true #[qt2]))
  let orderA := `ConstProbe.OrderA
  let orderB := `ConstProbe.OrderB
  let d1 := definitionInfo `Fixture.firstConflict
  let d2 := definitionInfo `Fixture.secondConflict
  arts := arts.insert orderA (← saveLegacy dir orderA (data false #[d1,d2]))
  arts := arts.insert orderB (← saveLegacy dir orderB (data false #[d2,d1]))
  let keys := #[`Fixture.P,`Fixture.w1,`Fixture.w2,`Fixture.q,`Fixture.hidden,`Fixture.unique,
    `Fixture.extra,`Fixture.laterExtra,`Fixture.absent]
  checkPair "legacy, axiom-to-theorem then later proof, earliest owner"
    #[{module := first},{module := second},{module := third}] arts .private keys fun env => do
      checkValue env `Fixture.q (some qt2)
      checkOwner env `Fixture.q 0
      checkOwner env `Fixture.extra 0
      checkOwner env `Fixture.laterExtra 2
  checkPair "legacy, theorem retained after weaker axiom"
    #[{module := first},{module := second},{module := weak}] arts .private keys fun env =>
      checkValue env `Fixture.q (some qt1)
  checkPair "module import all, public axiom/private theorem separation"
    #[{module := modernA,importAll := true},{module := modernB,importAll := true}]
    arts .exported keys fun env => do
      checkValue env `Fixture.q (some qt2)
      checkValue env `Fixture.q (some qa) (exported := true)
      checkValue env `Fixture.hidden (some hidden)
      checkValue env `Fixture.hidden none (exported := true)
      checkOwner env `Fixture.q 0
  checkPair "module public table upgrades axiom to theorem"
    #[{module := modernA,importAll := true},{module := modernRich}]
    arts .exported keys fun env => do
      checkValue env `Fixture.q (some qt2)
      checkValue env `Fixture.q (some qt2) (exported := true)
      checkOwner env `Fixture.q 0
  checkPair "module exported-only constants"
    #[{module := modernA},{module := modernB}] arts .exported keys fun env => do
      checkValue env `Fixture.q (some qa)
      checkValue env `Fixture.hidden none
  checkPair "module non-exported import stays private"
    #[{module := modernA,isExported := false},{module := modernUnique}]
    arts .exported keys fun env => do
      checkValue env `Fixture.q (some qa)
      checkValue env `Fixture.q none (exported := true)
      checkValue env `Fixture.unique (some unique) (exported := true)
  checkPair "server level" #[{module := modernA},{module := modernB}] arts .server keys fun env =>
    checkValue env `Fixture.q (some qa)
  checkPair "legacy root importing modern modules"
    #[{module := modernA},{module := modernB}] arts .private keys fun env =>
      checkValue env `Fixture.q (some qt2)
  checkPair "persistent marking occurs after helper join"
    #[{module := first},{module := second},{module := third}] arts .private keys
    (fun env => checkValue env `Fixture.q (some qt2)) (leakEnv := true)
  checkPair "empty tables" #[] {} .private #[] (fun _ => pure ())
  let malformed := `ConstProbe.Mismatched
  let malformedArt ← saveLegacy dir malformed
    { data false #[p] with constNames := #[`Fixture.P, `Fixture.unpaired] }
  checkPair "mismatched arrays retain zipped traversal"
    #[{ module := malformed }] (({} : NameMap ImportArtifacts).insert malformed malformedArt)
    .private #[`Fixture.P, `Fixture.unpaired] fun env => do
      checkValue env `Fixture.P (some p)
      checkValue env `Fixture.unpaired none
      unless env.const2ModIdx[`Fixture.unpaired]? == none do
        throw <| IO.userError "unpaired name acquired an owner"
  checkError "duplicate preserves earlier IR-extra owner"
    #[{module := extra},{module := conflict},{module := conflict2}] arts
    "import ConstProbe.Conflict2 failed, environment already contains 'Fixture.duplicate' from ConstProbe.Extra"
  checkError "later IR-extra name cannot alter earlier conflict"
    #[{module := conflict},{module := conflict2},{module := later}] arts
    "import ConstProbe.Conflict2 failed, environment already contains 'Fixture.duplicate' from ConstProbe.Conflict"
  checkError "first conflict follows original constant iteration order"
    #[{module := orderA},{module := orderB}] arts
    "import ConstProbe.OrderB failed, environment already contains 'Fixture.secondConflict' from ConstProbe.OrderA"
  IO.println "All constant table tests passed."

/-- A separate process mode that retains no imported references across freeRegions. -/
private unsafe def testFree (dir : FilePath) : IO Unit := do
  let name := `ConstProbe.Free
  let art ← saveLegacy dir name (data false #[ax `Fixture.free])
  let arts := ({} : NameMap ImportArtifacts).insert name art
  for _ in [:20] do
    let env ← load #[{module := name}] arts .private true
    env.freeRegions
  IO.println "Repeated parallel import/free completed."

end ImportConstantsProbe

unsafe def main : IO Unit := do
  let dir : FilePath := "_tmp_importConstants"
  ImportConstantsProbe.test dir
  ImportConstantsProbe.testFree dir
  IO.FS.removeDirAll dir
