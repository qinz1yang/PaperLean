import Lean

open Lean Elab Term

-- The atom and the parser's named pattern syntax have distinct elaborators.
run_meta do
  let env ← getEnv
  let atom := `Lean.Elab.Term.elabNamedPattern
  let registered (key : Name) :=
    (termElabAttribute.getEntries env key).any (fun e => e.declName == atom)
  unless registered `namedPattern && !registered `Lean.Parser.Term.namedPattern do
    throwError "named pattern elaborators registered under the wrong syntax kinds"
