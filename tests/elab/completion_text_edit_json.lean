import Lean.Server.Completion.CompletionItemCompression

open Lean Lean.Lsp in
#eval show IO Unit from do
  let range : Range := {
    start := { line := 0, character := 0 }
    «end» := { line := 0, character := 0 }
  }
  for text in ["plain", "a\"b", "a\\nb", "a\nb", "\t\r", String.singleton (Char.ofNat 0), "α🙂"] do
    let list : ResolvableCompletionList := {
      isIncomplete := false
      items := #[{ label := "edit", textEdit? := some { newText := text, insert := range, replace := range } }]
    }
    match Json.parse list.compressFast with
    | .error error => throw <| IO.userError error
    | .ok parsed =>
      unless parsed == toJson list do
        throw <| IO.userError s!"completion text changed during JSON serialization: {repr text}"
