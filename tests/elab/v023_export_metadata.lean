module

public meta import Lean.Declaration
public meta import Lean.Expr
meta import Lean.PaperLean.ExportJson
import LeanExport.Parse
import all LeanExport.Parse

open Lean

private def header := "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}"

private def parseText (text : String) : IO LeanExport.ExportedEnv := do
  let buf ← IO.mkRef { data := text.toUTF8 : IO.FS.Stream.Buffer }
  LeanExport.parseStream (.ofBuffer buf)

private def reject (text : String) (reason : String) : IO Unit := do
  let result : Option String ← try
      discard <| parseText text
      pure none
    catch e => pure (some e.toString)
  let some actual := result | throw <| IO.userError s!"accepted malformed export: {text}"
  unless (actual.splitOn reason).length > 1 do
    throw <| IO.userError s!"unexpected error: {actual}; expected {reason}"

#eval do
  -- A valid header alone is a valid empty environment, including EOF without a final newline.
  for text in [header, header ++ "\n", " \t" ++ header ++ " \r\n"] do
    let env ← parseText text
    unless env.constOrder.isEmpty && env.constMap.isEmpty do
      throw <| IO.userError "metadata-only export was not empty"
  -- Producer metadata is provenance, not a demand for this exact Lean/exporter executable.
  let provenance := "{\"meta\":{\"format\":{\"version\":\"3.1.0\"},\"lean\":{\"version\":\"other\"},\"exporter\":{\"name\":\"compatible\"}}}"
  discard <| parseText provenance
  for text in ["", "\n", "not JSON", "[]"] do
    reject text (if text == "[]" then "Expected JSON object" else "Invalid JSON")
  for text in ["{}", "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"x\"}}", "{\"meta\":false}",
      "{\"meta\":{},\"axiom\":{}}"] do
    reject text "Expected export metadata on first line"
  for text in ["{\"meta\":{}}", "{\"meta\":{\"format\":0}}"] do
    reject text "missing format object"
  for text in ["{\"meta\":{\"format\":{}}}", "{\"meta\":{\"format\":{\"version\":3}}}"] do
    reject text "missing format version"
  for version in ["", "3.0.0", "3.1.1", "4.0.0"] do
    reject ("{\"meta\":{\"format\":{\"version\":\"" ++ version ++ "\"}}}")
      "Unsupported export format version"
  reject (header ++ " trailing") "Invalid JSON"
  reject (header ++ header) "Invalid JSON"
  reject "{\"meta\":{},\"meta\":{}}" "duplicate object key"
  reject "{\"meta\":{\"format\":{\"version\":\"3.1.0\",\"\\u0076ersion\":\"3.1.0\"}}}"
    "duplicate object key"
  reject (header ++ "\n" ++ header) "Unknown export object"
  reject (header ++ "\n\n") "Invalid JSON"
  -- Existing names/levels zero are reserved; expression index zero remains available once.
  discard <| parseText (header ++ "\n{\"ie\":0,\"bvar\":0}\n")
  reject (header ++ "\n{\"in\":0,\"str\":{\"pre\":0,\"str\":\"x\"}}") "Name index 0 bound twice"
  reject (header ++ "\n{\"il\":0,\"succ\":0}") "Level index 0 bound twice"
  -- The recursor-rule helper has a separate index namespace even though present records inline rules.
  let buf ← IO.mkRef { data := ByteArray.empty : IO.FS.Stream.Buffer }
  let action : LeanExport.Parse.M Unit := do
    let rule : RecursorRule := { ctor := `ctor, nfields := 0, rhs := mkBVar 0 }
    LeanExport.Parse.addRecursorRule 0 rule
    LeanExport.Parse.addRecursorRule 0 rule
  let result : Option String ← try
      discard <| LeanExport.Parse.M.run action (.ofBuffer buf)
      pure none
    catch e => pure (some e.toString)
  unless result.any (fun (s : String) => (s.splitOn "RecursorRule index 0 bound twice").length > 1) do
    throw <| IO.userError "duplicate recursor rule was not rejected"
