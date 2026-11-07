# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
cd "$TMP_DIR"
cat > lakefile.lean <<'END'
import Lake
open Lake System
open Lake DSL
package headerorder
lean_lib Graph

-- The stock DFS visits Graph.A -> Graph.Child before Graph.B. Give Graph.B
-- its generated source in that ordering, and reject a premature request for it.
private def importsFacet : ModuleFacetDecl :=
  Lake.DSL.mkModuleFacetDecl (Array Lake.Module) `imports fun mod => do
    let late := mod.pkg.dir / "Graph" / "B.lean"
    if mod.name == `Graph.Child then
      IO.FS.writeFile late "module\npublic def generated := 17\n"
    if mod.name == `Graph.B && !(← late.pathExists) then
      error "Graph.B imports were requested before its generator Graph.Child"
    Lake.Module.importsFacetConfig.run mod

script order do
  let ws ← getWorkspace
  let custom := ws.addModuleFacetConfig importsFacet.config
  let some root := custom.findModule? `Graph | error "missing root"
  let result ← custom.runBuild <| root.lib.modules.fetch
  unless result.any (·.name == `Graph.Child) && result.any (·.name == `Graph.B) do
    error "missing module in completed traversal"
  return 0
END
mkdir -p Graph
printf 'module\npublic import Graph.A\npublic import Graph.B\n' > Graph.lean
printf 'module\npublic import Graph.Child\n' > Graph/A.lean
printf 'module\n' > Graph/Child.lean
rm -f Graph/B.lean
run env -u PAPERLEAN_ACCELERATE lake run order
rm -f Graph/B.lean
run env PAPERLEAN_ACCELERATE=1 lake run order
