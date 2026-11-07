# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
case "$(uname -s)" in MINGW*|MSYS*|CYGWIN*|Windows_NT) return 0 ;; esac
cd "$TMP_DIR"
export PAPERLEAN_CACHE_DIR="$PWD/user-cache"
unset PAPERLEAN_SOURCE_INPUT_CACHE
export PAPERLEAN_SOURCE_INPUT_STATS=1 LAKE_ARTIFACT_CACHE=false
mkdir project
cd project
cat > lakefile.lean <<'END'
import Lake
open System Lean Lake
open Lake DSL
package sourcecache
lean_lib Inputs

target generate pkg : Unit := Job.async do
  IO.FS.writeFile (pkg.dir / "Generated.lean")
    "module\n@[expose] public def generated := 17\n"
lean_lib Generated where needs := #[generate]
lean_lib Use

script report (args) do
  let [which, output] := args | error "report expects a module and filename"
  let ws ← getWorkspace
  let some mod := ws.findModule? (Name.str `Inputs which) | error "missing module"
  let input ← ws.runBuild <| mod.input.fetch
  let resolved := input.imports.map fun i => (i.module?.map (·.name))
  IO.FS.writeFile output <| (Json.mkObj [
    ("header", toJson input.header), ("hash", toJson input.trace.hash.toString),
    ("mtimeSec", toJson input.trace.mtime.sec), ("mtimeNs", toJson input.trace.mtime.nsec.toNat),
    ("resolved", toJson resolved)]).compress
  return 0

script generated do
  let ws ← getWorkspace
  let some generated := ws.findModule? `Generated | error "no generated module"
  let some useMod := ws.findModule? `Use | error "no consumer"
  discard <| ws.runBuild do
    discard (← useMod.input.fetch).await
    discard (← generated.lib.extraDep.fetch).await
    useMod.leanArts.fetch
  return 0
END
mkdir Inputs
printf '%s\n' module 'public import Inputs.One' 'meta import Inputs.«word.part»' > Inputs/Main.lean
printf '%s\n' module > Inputs/One.lean
printf '%s\n' module > Inputs/Two.lean
printf '%s\n' module > 'Inputs/word.part.lean'
printf '%s\n' module 'public import Inputs.Two' > Inputs/Other.lean
ln -s Main.lean Inputs/Alias.lean
printf '%s\n' module 'public import Generated' 'example : generated = 17 := rfl' > Use.lean

# Obtain the stock read, then leave source mtimes and ctimes older than the
# same-device clock by the cache's required two whole seconds.
run env -u PAPERLEAN_ACCELERATE lake run report Main before.json
[ ! -d "$PAPERLEAN_CACHE_DIR/prepared" ] || fail "plain Lake created a source cache"
python3 - <<'PYTHON'
import time
from pathlib import Path
stamp = max(p.lstat().st_ctime for p in Path('Inputs').iterdir())
time.sleep(max(0, int(stamp) + 3.1 - time.time()))
PYTHON
rec() { env PAPERLEAN_ACCELERATE=1 lake run report "$1" "$2" > "$3" 2>&1; }
rec Main prime.json prime.log || fail "cold capture failed"
grep -q 'hits=0 new=1' prime.log || fail "old regular source was not recorded"
rec Main hit.json hit.log || fail "replay failed"
grep -q 'hits=1 new=0' hit.log || fail "regular source was not reused"
cmp before.json hit.json || fail "trace, resolved imports or flags differed"
env PAPERLEAN_ACCELERATE=1 PAPERLEAN_SOURCE_INPUT_CACHE=0 lake run report Main off.json > off.log 2>&1 ||
  fail "explicit cache opt-out failed"
if grep -q 'PaperLean source inputs:' off.log; then fail "opt-out opened a source cache"; fi
cmp before.json off.json || fail "opt-out changed selected input"

# A symlink is read exactly as Lake does and never admitted.
rec Alias alias.json alias.log || fail "symlink read failed"
grep -q 'hits=0 new=0' alias.log || fail "symlink was cached"
ln -sfn Other.lean Inputs/Alias.lean
rec Alias alias2.json alias2.log || fail "retargeted symlink failed"
run env -u PAPERLEAN_ACCELERATE lake run report Alias alias-stock.json
cmp alias2.json alias-stock.json || fail "stale symlink replay"

# Preserve the source length and apparent mtime across a real import change.
python3 - <<'PYTHON'
from pathlib import Path
import os
p=Path('Inputs/Main.lean'); old=p.read_bytes(); st=p.stat()
new=old.replace(b'Inputs.One',b'Inputs.Two')
assert old != new and len(old) == len(new)
p.write_bytes(new); os.utime(p,ns=(st.st_atime_ns,st.st_mtime_ns))
PYTHON
rec Main fresh.json fresh.log || fail "changed source failed"
grep -q 'hits=0 new=0' fresh.log || fail "fresh ctime admitted/replayed old header"
run env -u PAPERLEAN_ACCELERATE lake run report Main fresh-stock.json
cmp fresh.json fresh-stock.json || fail "same mtime/size concealed changed bytes"

# Independent owners of the same trusted record can retire in either order.
rec One one.json one.log & a=$!
rec Other other.json other.log & b=$!
wait "$a" || fail "first concurrent owner failed"
wait "$b" || fail "second concurrent owner failed"
rec One one2.json one2.log || fail "first row after concurrent publication failed"
rec Other other2.json other2.log || fail "second row after concurrent publication failed"
cmp one.json one2.json && cmp other.json other2.json || fail "mixed concurrent cache results"

record=$(find "$PAPERLEAN_CACHE_DIR/prepared" -path '*/inputs/*.paperlean' -type f)
[ -f "$record" ] || fail "expected one per-user record"
printf 'incomplete' > "$record"
rec Other after.json after.log || fail "corrupt record did not fall back"
grep -q 'hits=0 new=1' after.log || fail "corrupt record reused"
cmp other.json after.json || fail "corruption changed selected input"

# mtime can also be preserved while a previously successful UTF-8 source goes bad.
printf '\377' > Inputs/Other.lean
if env PAPERLEAN_ACCELERATE=1 lake run report Other rejected.json > bad.log 2>&1; then
  fail "invalid UTF-8 accepted through a cached header"
fi
grep -q 'non UTF-8' bad.log || fail "missing ordinary read error"
[ ! -f Generated.lean ] || fail "generated source already exists"
run env PAPERLEAN_ACCELERATE=1 lake run generated
