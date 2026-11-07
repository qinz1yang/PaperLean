/- Copyright (c) 2026 PaperLean contributors. Released under Apache 2.0 license. -/
import Lean.PaperLean.ImportState

open Lean in
@[extern "paperlean_test_replay_ownership"]
opaque checkReplay (name : @& Name) (entries : @& Array (Array EnvExtensionEntry)) : BaseIO Bool

open Lean in
unsafe def main (args : List String) : IO Unit := do
  Lean.initSearchPath args[0]!
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := args[1]!.toName }] {} (leakEnv := true) (loadExts := true)
  let name := `Lean.Meta.simpExtension
  let some descr := (← persistentEnvExtensionsRef.get).find? (·.name == name)
    | throw (IO.userError "missing simp extension")
  let entries := (descr.toEnvExtension.getState (asyncMode := .sync) env).importedEntries
  unless ← checkReplay name entries do throw (IO.userError "unexpected replay ownership")
