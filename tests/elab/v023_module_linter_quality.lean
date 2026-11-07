import Lean

open Lean Elab Command

run_cmd do
  let oldLinters ← moduleLintersRef.get
  let oldState ← get
  try
    moduleLintersRef.set #[{
      name := `v023ModuleMetric
      run := fun _ => do
        Linter.logCodeQualityEntry {
          name := "v023ModuleMetric"
          source := .module `v023Module
          value := .scalar 17.0
        }
    }]
    for async in [false, true] do
      set { oldState with snapshotTasks := #[], codeQualityEntryTasks := #[] }
      withScope (fun s => { s with opts := s.opts.setBool `Elab.async async }) do
        let terminal := mkNode ``Parser.Command.eoi #[]
        withReader (fun ctx => { ctx with snap? := none }) do
          runLintersAsync terminal #[]
        let tasks := (← get).codeQualityEntryTasks
        unless tasks.size == 2 do throwError "missing linter result tasks"
        -- The module result must contain the same metric in synchronous and asynchronous mode.
        let entries := tasks[1]!.get
        unless entries.any (·.entry.name == "v023ModuleMetric") do
          throwError "module metric was lost (async={async})"
  finally
    moduleLintersRef.set oldLinters
    set oldState
