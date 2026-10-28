# Tests that code compiled against the library calls upstream functions that PaperLean changed as it
# calls them in official Lean 4.35.0-rc3: the calling conventions recorded in the library's `.olean`
# files (IR signatures with borrow flags) are upstream's, also for the functions with hooks that
# record environment accesses (`Lean.PaperLean.EnvDeps`). The full comparison with official Lean is
# the gate's interface check.

cat > "$TMP_DIR/Interface.lean" <<'EOF'
import Lean
open Lean

def irHeader (d : IR.Decl) : String :=
  let ps := d.params.map fun p => s!"{if p.borrow then "@&" else ""}{format p.ty}"
  s!"{d.name} {ps} -> {format d.resultType}"

def main : IO Unit := do
  let lib ← getLibDir (← findSysroot (lean := (← IO.appPath).toString))
  for (file, names) in [("Lean/Util/Path.olean", [`Lean.SearchPath.findWithExt, `Lean.SearchPath.findModuleWithExt]),
      ("Lean/Environment.olean", [`Lean.finalizeImport])] do
    let (md, _) ← readModuleData (lib / file)
    for (ext, es) in md.entries do
      if ext == `Lean.IR.declMapExt then
        for e in es do
          let d : IR.Decl := unsafe unsafeCast e
          if names.contains d.name then IO.println (irHeader d)
  -- functions with hooks that record environment accesses
  initSearchPath (← findSysroot (lean := (← IO.appPath).toString))
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Lean }] {} (loadExts := true)
  for n in [`Lean.ScopedEnvExtension.getState, `Lean.Environment.findAsync?, `Lean.Environment.find?,
      `Lean.Environment.contains, `Lean.ResolveName.resolveGlobalName, `Lean.TagAttribute.hasTag,
      `Lean.PersistentEnvExtension.getState._redArg, `Lean.Environment.toKernelEnv,
      `Lean.ResolveName.resolveNamespace] do
    if let some d := IR.findEnvDecl env n then IO.println (irHeader d)
EOF
capture lean --run "$TMP_DIR/Interface.lean"
check_out_contains "Lean.SearchPath.findWithExt #[tobj, @&obj, tobj, void] -> obj"
check_out_contains "Lean.SearchPath.findModuleWithExt #[tobj, @&obj, tobj, void] -> obj"
check_out_contains "Lean.finalizeImport #[@&obj, obj, obj, u32, u8, u8, u8, u8, u8, void] -> obj"
# (official Lean's signatures)
check_out_contains "Lean.ScopedEnvExtension.getState #[◾, ◾, ◾, @&tobj, @&obj, obj, @&tobj] -> tobj"
check_out_contains "Lean.Environment.findAsync? #[obj, tobj, u8] -> tobj"
check_out_contains "Lean.Environment.find? #[obj, tobj, u8] -> tobj"
check_out_contains "Lean.Environment.contains #[obj, tobj, u8] -> u8"
check_out_contains "Lean.ResolveName.resolveGlobalName #[obj, @&obj, tobj, tobj, tobj] -> tobj"
check_out_contains "Lean.TagAttribute.hasTag #[@&obj, obj, tobj] -> u8"
check_out_contains "Lean.PersistentEnvExtension.getState._redArg #[tobj, @&obj, obj, @&tobj, tobj] -> tobj"
check_out_contains "Lean.Environment.toKernelEnv #[obj] -> obj"
check_out_contains "Lean.ResolveName.resolveNamespace #[obj, tobj, tobj, tobj] -> tobj"
