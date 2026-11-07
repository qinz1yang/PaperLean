import Lean
import Lean.PaperLean.GraphDiff
import Lean.PaperLean.OLeanPack
import Lean.PaperLean.System

open Lean Parser
abbrev ParserRows := Array (Array (ScopedEnvExtension.Entry ParserExtension.OLeanEntry))
abbrev ParserStack := ScopedEnvExtension.StateStack
  ParserExtension.OLeanEntry ParserExtension.Entry ParserExtension.State

unsafe def equalGraph {α : Type} (a b : α) : IO Unit := do
  if let some why := PaperLean.graphDiff a b true then throw <| IO.userError why

def require (p : Bool) (msg : String) : IO Unit :=
  unless p do throw <| IO.userError msg

unsafe def checkFold (env : Environment) (tag : String) (rows : ParserRows) : IO (Option ParserStack) := do
  let ctx : ImportM.Context := { env, opts := {} }
  let reference ← (ScopedEnvExtension.addImportedFn parserExtension.descr rows ctx).toBaseIO
  IO.eprintln s!"parser-probe begin {tag}"
  let actual ← (parserExtension.ext.addImportedFn rows ctx).toBaseIO
  IO.eprintln s!"parser-probe end {tag}"
  match reference, actual with
  | .ok a, .ok b => equalGraph a b; return some b
  | .error a, .error b =>
    require (toString a == toString b) "different parser error"
    return none
  | _, _ => throw <| IO.userError s!"different fold outcome: {tag}"

unsafe def main (args : List String) : IO Unit := do
  if let ["make", dir, out] := args then
    IO.FS.createDirAll dir
    let row := Array.replicate 4096 (ScopedEnvExtension.Entry.global (ParserExtension.OLeanEntry.token "§prefix"))
    let entries := #[(``Lean.Parser.parserExtension, row)]
    let data : ModuleData := {
      isModule := false
      imports := #[]
      constNames := #[]
      constants := #[]
      extraConstNames := #[]
      entries := unsafeCast entries
    }
    saveModuleData ((dir : System.FilePath) / "Dense.olean") `Dense data
    let n ← Lean.PaperLean.OLeanPack.create #[dir] out (baseAddr := 0x200000000000)
    require (n == 1) "dense fixture missing from pack"
    return
  Lean.initSearchPath args[0]!
  Lean.enableInitializersExecution
  let env ← importModules #[{module := `Dense}, {module := `TokenScope}] {} (leakEnv := true) (loadExts := true)
  require (parserExtension.ext.name == `Lean.Parser.parserExtension) "parser extension was renamed"
  if args[1]? == some "fault" then
    -- Arm the injector after importing all other extensions; exercise only the registered parser.
    PaperLean.setEnv "PAPERLEAN_IMPORT_CHECK_FAULT" (some "state")
    discard <| parserExtension.ext.addImportedFn (parserExtension.ext.getImportedEntries env) {env, opts := {}}
    throw <| IO.userError "parser checker accepted the injected discrepancy"
  let some real ← checkFold env "real" (parserExtension.ext.getImportedEntries env)
    | throw <| IO.userError "real parser fold failed"
  let env := parserExtension.ext.setState env real
  require ((getTokenTable env).find? "◆paperleanScoped").isNone "scoped keyword active too early"
  require (runParserCategory env `term "◆paperleanScoped" matches .error _) "scoped parser active too early"
  let env := parserExtension.activateScoped env `ParserTokenScope
  let .ok stx := runParserCategory env `term "◆paperleanScoped" | throw <| IO.userError "scoped parser missing"
  require (stx.getKind == `ParserTokenScope.marker) "wrong scoped parser"
  let env := parserExtension.addLocalEntry (parserExtension.pushScope env) (.token "◆paperleanLocal")
  require (((getTokenTable env).find? "◆paperleanLocal").isSome) "local keyword missing"
  let env := parserExtension.popScope env
  require (((getTokenTable env).find? "◆paperleanLocal").isNone) "local keyword escaped"
  let some idx := env.getModuleIdx? `Dense | throw <| IO.userError "missing dense fixture"
  require (idx.toNat < 16) "dense row is outside the hint window"
  let some row := (parserExtension.ext.getImportedEntries env)[idx.toNat]? | throw <| IO.userError "missing parser row"
  let dense : ParserRows := (Array.replicate idx.toNat #[]).push row
  let sparse : ParserRows := #[(Array.range 4096).map fun i => .global (.token s!"§unique{i}")]
  let some _ ← checkFold env "sparse" sparse | throw <| IO.userError "sparse fold failed"
  let some _ ← checkFold env "small" #[#[.global (.token "§prefix"), .global (.token "§prefix")]]
    | throw <| IO.userError "small fold failed"
  let scopedRow : Array (ScopedEnvExtension.Entry ParserExtension.OLeanEntry) := #[
    .global (.token "§prefixLong"),
    .scoped `ScopeOnly (.token "§local"),
    .scoped `ScopeOnly (.token "§local")]
  let some regular ← checkFold env "dense" (dense.push scopedRow)
    | throw <| IO.userError "dense fold failed"
  let t := getTokenTable (parserExtension.ext.setState env regular)
  require (t.matchPrefix "§prefixLonger" 0 == some "§prefixLong" && (t.find? "§local").isNone) "invalid trie"
  for (tag, invalid) in #[("empty", ParserExtension.OLeanEntry.token ""),
      ("badCategory", .parser `MissingCategory `Lean.Parser.Term.ident 100)] do
    let some recovered ← checkFold env tag (dense.push #[.global invalid, .global (.token "§prefix")])
      | throw <| IO.userError "unexpected exception after malformed token or category"
    require (((getTokenTable (parserExtension.ext.setState env recovered)).find? "§prefix").isSome)
      "token not restored after malformed input"
  let failed ← checkFold env "badConstant" (dense.push #[.global (.parser `MissingCategory `MissingParser 100)])
  require failed.isNone "missing parser was accepted"
  IO.println "parser token folds agree"
