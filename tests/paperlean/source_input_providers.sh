# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
cd "$TMP_DIR"
export PAPERLEAN_SOURCE_INPUT_CACHE=1 PAPERLEAN_SOURCE_INPUT_STATS=1 LAKE_ARTIFACT_CACHE=false
mkdir -p workspace/other
cd workspace
cat > lakefile.lean <<'LEAN'
import Lake
open Lake Lean
open Lake DSL
package providerFacts
lean_lib TargetValue
lean_lib RealDep
lean_lib OtherDep

private def claimed (m : Lake.Module) (base : ModuleInput) : ModuleInput :=
  let imp : ModuleImport := {module := `Counterfeit, isMeta := true, module? := none}
  {base with
    path := m.leanFile.addExtension "claimed"
    trace := {base.trace with hash := .ofText "fabricated hash"}
    header := {isModule := false, imports := #[imp.toImport]}
    imports := #[imp]}

private def runCustom (fabricated : Bool) (m : Lake.Module) : FetchM (Job ModuleInput) := do
  if fabricated then
    let base : ModuleInput := {
      path := m.leanFile
      trace := .nil "fake"
      header := {isModule := false, imports := #[]}
      imports := #[]}
    return Job.pure (claimed m base)
  let original ← Lake.Module.inputFacetConfig.run m
  return original.map fun value => claimed m value

private def custom (fabricated : Bool) : ModuleFacetDecl :=
  Lake.DSL.mkModuleFacetDecl ModuleInput `input (runCustom fabricated)

private def report (input : ModuleInput) : IO Unit :=
  IO.println s!"FACT {input.path} {input.trace.hash} {input.header.isModule} {input.header.imports} {input.imports.map (·.module)}"

script observe (args) do
  let [mode] := args | error "expected mode"
  let ws ← getWorkspace
  let some m := ws.findModule? `TargetValue | error "missing module"
  if mode == "real" then
    report (← ws.runBuild m.input.fetch)
  else if mode == "detached" then
    let copy := { m with lib := { m.lib with pkg := { m.pkg with dir := ws.dir / "other" } } }
    ws.runBuild do
      let other ← (← Lake.Module.inputFacetConfig.run copy).await
      unless other.header.imports.any (·.module == `OtherDep) do error "alternate source was never read"
      let ghost ← (← runCustom true m).await
      unless ghost.header.imports.any (·.module == `Counterfeit) do error "detached fake was never returned"
      return Job.pure ()
  else
    let w := ws.addModuleFacetConfig (custom (mode == "fabricated")).config
    report (← w.runBuild m.input.fetch)
  return 0
LEAN
printf 'module\npublic meta import all RealDep\n' > TargetValue.lean
printf 'module\npublic import OtherDep\n' > other/TargetValue.lean
printf 'module\n' > RealDep.lean
printf 'module\n' > OtherDep.lean
sleep 3
env PAPERLEAN_ACCELERATE=0 lake run observe real > "$TMP_DIR/reference" 2>&1 || fail "stock input query failed"
grep '^FACT ' "$TMP_DIR/reference" > "$TMP_DIR/wanted" || fail "stock query produced no facts"
for mode in wrapper fabricated detached; do
  export PAPERLEAN_CACHE_DIR="$TMP_DIR/private-$mode"
  mkdir -p "$PAPERLEAN_CACHE_DIR"
  env PAPERLEAN_ACCELERATE=1 lake run observe "$mode" > "$TMP_DIR/$mode.first" 2>&1 || fail "custom input failed"
  if [ "$mode" != detached ]; then
    grep -q '^FACT .*claimed.*false.*Counterfeit' "$TMP_DIR/$mode.first" || fail "custom provider was not selected"
  fi
  for phase in reopened warm; do
    env PAPERLEAN_ACCELERATE=1 lake run observe real > "$TMP_DIR/$mode.$phase" 2>&1 || fail "ordinary input query failed"
    grep '^FACT ' "$TMP_DIR/$mode.$phase" > "$TMP_DIR/actual" || fail "ordinary input query produced no facts"
    cmp "$TMP_DIR/wanted" "$TMP_DIR/actual" || fail "$mode contaminated ordinary path, header or trace"
  done
  grep -Eq 'PaperLean source inputs: hits=[1-9]' "$TMP_DIR/$mode.warm" || fail "$mode did not exercise a real private cache hit"
done
