# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
export LAKE_ARTIFACT_CACHE=false
export PAPERLEAN_SETUP_INDEX_KEEP=1
root="$(cd "$TMP_DIR" && pwd -P)"
mkdir -p "$root/alt/CaseProbe" "$root/provider" "$root/main/CaseProbe"

# An unrelated module facet still permits a shared index. These artifacts provide
# a second version of the same module and package for the custom export facet.
cd "$root/alt"
cat > lakefile.lean <<'END'
import Lake
open Lake DSL
package facetbug
@[default_target] lean_lib CaseProbe
module_facet extra (_mod) : Unit := pure <| Job.pure ()
END
printf 'module\n@[expose] public def leaf := 17\n' > CaseProbe/Leaf.lean
printf 'module\npublic import CaseProbe.Leaf\n' > CaseProbe.lean
run lake paperlean build
ls .lake/paperlean-setup/*/setup-*.paperlean >/dev/null || fail "unrelated facet disabled the index"
export TEST_ALT_ARTIFACTS="$root/alt/.lake/build/lib/lean/CaseProbe"

# A dependency can replace a facet used by every package in the workspace.
cd "$root/provider"
cat > lakefile.lean <<'END'
import Lake
open Lake Lean System
open Lake DSL
package provider
@[«module_facet»] def customExport : ModuleFacetDecl :=
  Lake.DSL.mkModuleFacetDecl ModuleExportInfo `exportInfo fun mod => do
    (← Lake.Module.exportInfoFacetConfig.run mod).mapM fun info => do
      if mod.name != `CaseProbe.Leaf then return info
      let some dir ← IO.getEnv "TEST_ALT_ARTIFACTS" | error "missing alternative artifacts"
      let replace (arts : ImportArtifacts) := ImportArtifacts.ofArrays <|
        arts.toArrays.map fun parts => parts.map fun path => (dir : FilePath) / path.fileName.get!
      return {info with arts := replace info.arts, allArts := replace info.allArts}
END

cd "$root/main"
cat > lakefile.toml <<'END'
name = "facetbug"
defaultTargets = ["CaseProbe"]
[[require]]
name = "provider"
path = "../provider"
[[lean_lib]]
name = "CaseProbe"
END
printf 'module\n@[expose] public def leaf := 7\n' > CaseProbe/Leaf.lean
cat > CaseProbe/Middle.lean <<'END'
module
public import CaseProbe.Leaf
example : leaf = 17 := rfl
END
cat > CaseProbe.lean <<'END'
module
public import CaseProbe.Middle
example : leaf = 17 := rfl
END
run lake build
for mod in CaseProbe.Middle CaseProbe; do
  lake query "+$mod:setup" --json > "$root/$mod.json" || fail "query $mod"
done
rm -rf .lake/build
run lake paperlean build

cat > "$root/ReadSetup.lean" <<'END'
import Lean.Setup
open Lean
def main (args : List String) : IO Unit := do
  let [side] := args | throw <| IO.userError "need a setup file"
  IO.println (toJson (← ModuleSetup.load side).importArts).compress
END
for mod in CaseProbe.Middle CaseProbe; do
  ir="${mod//./\/}"
  lean --run "$root/ReadSetup.lean" ".lake/build/ir/$ir.setup.paperlean" > "$root/$mod.actual" || fail "read $mod"
  python3 - "$root/$mod.json" "$root/$mod.actual" "$TEST_ALT_ARTIFACTS/Leaf.olean" <<'PY'
import json
from pathlib import Path
import sys
expected = json.loads(Path(sys.argv[1]).read_text())["importArts"]
actual = json.loads(Path(sys.argv[2]).read_text())
assert expected["CaseProbe.Leaf"][0][0] == sys.argv[3], expected
assert actual == expected, (actual, expected)
PY
done
