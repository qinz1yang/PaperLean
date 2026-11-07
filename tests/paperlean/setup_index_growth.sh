# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
# Default CTest is small. SETUP_GROWTH_SIZE=1024 also reports the
# retained bytes and allocated blocks at 256, 512 and 1024 growing modules.
root="$(cd "$TMP_DIR" && pwd -P)"
n="${SETUP_GROWTH_SIZE:-12}"
export LAKE_ARTIFACT_CACHE=false
export PAPERLEAN_SETUP_INDEX_KEEP=1
cat > "$root/project.lean" <<'END'
import Lake
open Lean Lake System
open Lake DSL
package growth
@[default_target] lean_lib Bench

private def checkArts (mod : Lake.Module) : FetchM Unit := do
  let selected ← (← mod.setup.fetch).await
  let file := mod.irPath "setup.paperlean"
  let actual ← Lean.ModuleSetup.load file
  unless toJson actual.importArts == toJson selected.importArts do
    error s!"{mod.name}: decoded setup differs from Lake"
  unless ← file.pathExists do error s!"no accelerated file for {mod.name}"
  IO.println s!"verified {mod.name}: {actual.importArts.size} imports"

private def stats (mode : String) (count : Nat) : IO Unit := do
  IO.print (← IO.Process.run {cmd := "python3", args := #["stats.py", mode, toString count]})

script static (args) do
  let [n] := args | error "expected module count"
  let some n := n.toNat? | error "expected module count"
  let ws ← getWorkspace
  let some root := ws.findModule? `Bench | error "missing Bench"
  discard <| ws.runBuild do
    discard <| (← root.leanArts.fetch).await
    checkArts root
    stats "static" n
    return Job.pure ()
  return 0

script growing (args) do
  let [n] := args | error "expected module count"
  let some n := n.toNat? | error "expected module count"
  let ws ← getWorkspace
  discard <| ws.runBuild do
    for i in [0:n] do
      let name := Name.str `Bench s!"M{i}"
      let some mod := ws.findModule? name | error s!"no module {name}"
      let source := if i == 0 then
        "module\n@[expose] public def base : Nat := 17\n"
        else s!"module\npublic import Bench.M{i-1}\nexample : base = 17 := rfl\n"
      IO.FS.writeFile mod.leanFile source
      discard <| (← mod.leanArts.fetch).await
      if i+1 == n || [256, 512, 1024].contains (i+1) then
        checkArts mod
        stats "growing" (i+1)
    return Job.pure ()
  return 0

-- The first layout sees Late's old source without scheduling its input.
-- Its actual source then acquires a new transitive import before stock Lake reads it.
script changed do
  let ws ← getWorkspace
  let some root := ws.findModule? `Bench | error "no root"
  let some early := ws.findModule? `Bench.Early | error "no early module"
  let some late := ws.findModule? `Bench.Late | error "no late module"
  discard <| ws.runBuild do
    discard <| (← root.input.fetch).await
    discard <| (← early.leanArts.fetch).await
    IO.FS.writeFile late.leanFile "module\npublic import Bench.Leaf\nexample : leaf = 17 := rfl\n"
    discard <| (← root.leanArts.fetch).await
    checkArts late
    checkArts root
    return Job.pure ()
  return 0

script odd do
  let ws ← getWorkspace
  let some root := ws.findModule? `Bench | error "no root"
  let some dep := ws.findModule? (.str `Bench "Late\\Leaf") | error "no dependency"
  discard <| ws.runBuild do
    discard <| (← root.leanArts.fetch).await
    for mod in #[dep, root] do
      checkArts mod
      let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile (mod.irPath "setup.paperlean"))
      let actual ← IO.ofExcept <| Lean.PaperLean.setupFromJsonCompact? json
      if actual.importArts.contains .anonymous then error "unsupported path had an indexed setup"
    return Job.pure ()
  return 0
END
cat > "$root/stats.py" <<'END'
from pathlib import Path
import json
import sys

mode = sys.argv[1]
count = int(sys.argv[2])
directory = Path('.lake/paperlean-setup')
files = list(directory.glob('*/*.paperlean'))
bases = [f for f in files if f.name.startswith('setup-') and not f.name.startswith('setup-node-')]
nodes = [f for f in files if f.name.startswith('setup-node-')]
assert len(bases) == 1, (mode, count, bases)
if mode == 'static':
    assert not nodes, (mode, count, nodes)
if mode == 'growing':
    assert len(nodes) == count - 1, (mode, count, len(nodes))
if mode == 'changed':
    assert len(nodes) >= 2, (mode, count, nodes)

shared = [*bases, *nodes, *directory.glob('*/*.validated')]
sides = list(Path('.lake/build').rglob('*.setup.paperlean'))
def sizes(paths):
    return {'bytes': sum(p.stat().st_size for p in paths),
            'allocated': sum(p.stat().st_blocks * 512 for p in paths)}
print(json.dumps({'mode': mode, 'modules': count, 'bases': len(bases), 'nodes': len(nodes),
                  'shared': sizes(shared), 'module_setups': sizes(sides)}, sort_keys=True))
END
for d in static growing changed odd; do
  mkdir -p "$root/$d/Bench"
  cp "$root/project.lean" "$root/$d/lakefile.lean"
  cp "$root/stats.py" "$root/$d/stats.py"
done
cd "$root/static"
python3 - "$n" <<'PYTHON'
import sys
from pathlib import Path
n = int(sys.argv[1])
assert n >= 2
for i in range(n - 1):
    Path(f'Bench/M{i}.lean').write_text(f'module\npublic def x{i} := {i}\n')
Path('Bench.lean').write_text('module\n' + ''.join(f'public import Bench.M{i}\n' for i in range(n - 1)))
PYTHON
run env PAPERLEAN_ACCELERATE=1 lake run static "$n"

cd "$root/growing"
run env PAPERLEAN_ACCELERATE=1 lake run growing "$n"

cd "$root/changed"
printf 'module\npublic import Bench.Early\npublic import Bench.Late\n' > Bench.lean
printf 'module\n' > Bench/Early.lean
printf 'module\n' > Bench/Late.lean
printf 'module\n@[expose] public def leaf := 17\n' > Bench/Leaf.lean
run env PAPERLEAN_ACCELERATE=1 lake run changed
run python3 stats.py changed 4

# On POSIX this is a legal one-component module name. Conservative writer policy
# leaves it and its importer on stock Lake setups; both real artifacts must agree.
if [ "$(uname -s)" != Windows_NT ]; then
  cd "$root/odd"
  printf '%s\n' module 'public import Bench.«Late\Leaf»' 'example : unusual = 17 := rfl' > Bench.lean
  printf '%s\n' module '@[expose] public def unusual := 17' > 'Bench/Late\Leaf.lean'
  run env PAPERLEAN_ACCELERATE=1 lake run odd
fi
