# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
cd "$TMP_DIR"
export LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=false LAKE_CACHE_DIR="$PWD/artifacts" PAPERLEAN_SETUP_INDEX_KEEP=1
cat > lakefile.lean <<'LEAN'
import Lake
import Lake.PaperLean.SetupIndex
open Lake System
open Lake DSL
package lazySelected
@[default_target] lean_lib Top

private def hasExport (mod : Lake.Module) : FetchM Bool :=
  .mk fun _ _ _ store _ => return (← store.get).contains mod.exportInfo.key

script warm do
  let ws ← getWorkspace
  let some leaf := ws.findModule? `Top.Leaf | error "missing leaf"
  let some top := ws.findModule? `Top | error "missing root"
  discard <| ws.runBuild do
    discard <| (← leaf.input.fetch).await
    unless (← PaperLean.SetupIndex.indexFor ws.dir leaf).isSome do error "missing eligible input-only index"
    if ← hasExport leaf then error "header query started an export job"
    discard <| (← leaf.leanArts.fetch).await
    if ← hasExport leaf then error "leaf compile unexpectedly fetched its own exports"
    let before ← PaperLean.SetupIndex.moved
    if before.contains leaf.name then error "coverage attributed exports before their job was selected"
    let built ← top.leanArts.fetch
    discard <| built.await
    unless ← hasExport leaf do error "importer's setup never selected leaf's export"
    unless (← PaperLean.SetupIndex.moved).contains leaf.name do error "cached root did not certify its later moved exports"
    return built
  return 0
LEAN
mkdir -p Top
printf 'module\n@[expose] public def leaf := 7\n' > Top/Leaf.lean
printf 'module\npublic import Top.Leaf\nexample : leaf = 7 := rfl\n' > Top.lean
run env PAPERLEAN_ACCELERATE=1 lake run warm
for n in Top/Leaf Top; do
  grep -q 'paperlean-setup' ".lake/build/ir/$n.setup.paperlean" || fail "$n missed the index fast path"
done
grep -q "$LAKE_CACHE_DIR" .lake/build/ir/Top.setup.paperlean || fail "selected cache artifact missing from indexed root"
cat > GetArts.lean <<'LEAN'
import Lean.Setup
open Lean
def main (args : List String) : IO Unit := do
  let [file] := args | throw (IO.userError "missing setup")
  IO.println (toJson (← ModuleSetup.load file).importArts).compress
LEAN
lake query +Top:setup --json > stock-setup.json
lake env lean --run GetArts.lean stock-setup.json > stock-arts
lake env lean --run GetArts.lean .lake/build/ir/Top.setup.paperlean > actual-arts
cmp actual-arts stock-arts || fail "promoted moved export differs from Lake's complete setup"
