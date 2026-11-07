# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
cd "$TMP_DIR"
export LAKE_ARTIFACT_CACHE=false
cat > lakefile.lean <<'END'
import Lake
open Lake DSL
package ordering

target generate pkg : Unit := Job.async (prio := .dedicated) do
  IO.FS.writeFile (pkg.dir / "Generated.lean") "module\n@[expose] public def generated := 17\n"

lean_lib Generated where needs := #[generate]
@[default_target] lean_lib Use

script ordering do
  let ws ← getWorkspace
  let some useMod := ws.findModule? `Use | error "missing Use"
  let some generated := ws.findModule? `Generated | error "missing Generated"
  discard <| ws.runBuild do
    discard <| (← useMod.input.fetch).await
    -- If a parser eagerly scheduled the generated input, let that attempt
    -- finish while the source is absent. Ordinary Lake has no such job.
    let prior? ← (fetch? generated.input.key : FetchM (Option (Job (BuildData generated.input.key))))
    if let some prior := prior? then discard <| IO.wait prior.task
    discard <| (← generated.lib.extraDep.fetch).await
    useMod.leanArts.fetch
  return 0
END
printf 'module\npublic import Generated\nexample : generated = 17 := rfl\n' > Use.lean
rm -f Generated.lean
run env -u PAPERLEAN_ACCELERATE lake run ordering
rm -rf .lake/build
rm -f Generated.lean
run env PAPERLEAN_ACCELERATE=1 lake run ordering
