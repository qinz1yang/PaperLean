# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests the cache of prepared data that workspaces share (`Lake.PaperLean.Cache`): two workspaces with
# the same files of a dependency (here copies of one built package, as two workspaces that download
# the same release have) use one pack and one native library of the cache, which the second
# `paperlean prepare` neither packs nor compiles again. Each workspace reads the pack through a binding
# of its own, and the results are those without prepared data.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN
ROOT="$(cd "$TMP_DIR" && pwd -P)"
CACHE="$PAPERLEAN_CACHE_DIR/prepared"
mkdir -p "$ROOT/ws1/dep/Dep"
cd "$ROOT/ws1"
cat > dep/lakefile.toml <<'END'
name = "dep"
defaultTargets = ["Dep"]
[[lean_lib]]
name = "Dep"
END
printf 'def base (n : Nat) : Nat := n + 1\n' > dep/Dep/Base.lean
cat > dep/Dep/Twice.lean <<'END'
import Lean
macro "twice! " x:term : term => `($x + $x)
END
printf 'import Dep.Base\nimport Dep.Twice\n' > dep/Dep.lean
cat > lakefile.toml <<'END'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "dep"
path = "dep"
[[lean_lib]]
name = "Root"
END
cat > Root.lean <<'END'
import Dep
import Lean.PaperLean.OLeanPack
#eval twice! base 20
#eval show IO Unit from do
  let (served, _) ← Lean.PaperLean.OLeanPack.stats
  IO.println s!"served from packs: {if served > 0 then "some" else "none"}"
END
run lake build Dep
capture lake lean Root.lean
cp "$CAPTURED.out.produced" "$TMP_DIR/plain.out"
grep -q "served from packs: none" "$TMP_DIR/plain.out" || fail "plain lake read from packs"
cp -pR "$ROOT/ws1" "$ROOT/ws2"

entries() { grep -o '"prepared/[^"]*/\(pack\|native\)/dep-[0-9a-f]*' .lake/paperlean/env.json | sort -u; }
# The output of the root module with the prepared data: as without it, with packs and dep's library.
check_use() {
  capture env PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean Root.lean
  check_out_matches "paperlean-timing native libs=1 "
  { grep -v "^paperlean-" "$CAPTURED.out.produced" || true; } | sed 's/served from packs: some/served from packs: none/' |
    $DIFF -- "$TMP_DIR/plain.out" - || fail "the prepared data changes the output in $1"
  check_out_contains "served from packs: some"
}

capture lake paperlean prepare -j 2
check_out_contains "Packing dep"
check_out_contains "Compiling the native library of dep"
check_use ws1
E1=$(entries)
[ "$(echo "$E1" | wc -l | tr -d ' ')" = 2 ] || fail "env.json does not list a pack and a library of dep: $E1"

# The second workspace finds dep's data in the cache.
cd "$ROOT/ws2"
capture lake paperlean prepare -j 2
check_out_contains "Prepared"
! grep -q "Packing dep" "$CAPTURED.out.produced" || fail "the second workspace packed dep again"
! grep -q "Compiling the native library" "$CAPTURED.out.produced" || fail "the second workspace compiled again"
[ "$(entries)" = "$E1" ] || fail "the workspaces use different entries: $E1 and $(entries)"
[ "$(ls -d "$CACHE"/*/pack/dep-* | wc -l | tr -d ' ')" = 1 ] || fail "not one pack of dep: $(ls "$CACHE"/*/pack)"
[ "$(ls -d "$CACHE"/*/native/dep-* | wc -l | tr -d ' ')" = 1 ] || fail "not one library of dep: $(ls "$CACHE"/*/native)"
ls -d "$CACHE"/*/pack/.tmp-* "$CACHE"/*/native/.tmp-* 2> /dev/null && fail "temporary directories were left"
# each workspace binds the pack to its own files
[ -f .lake/paperlean/bind/dep-*.paperlean ] || fail "ws2 has no binding of its own"
capture lake paperlean status
check_out_matches "package dep: prepared: pack dep-[0-9a-f]+ of the cache \([0-9]+ modules\), native library dep-[0-9a-f]+"
check_out_contains "Lean's library: packed"
check_use ws2

# The first workspace's files do not matter to the second: deleting them leaves the second's results.
rm -rf "$ROOT/ws1"
check_use "ws2 without ws1"

# A prepare that finds everything in the cache changes nothing.
cp .lake/paperlean/env.json "$TMP_DIR/env.before"
capture lake paperlean prepare
! grep -q "Packing\|Compiling\|Writing the import image" "$CAPTURED.out.produced" ||
  fail "a prepare with nothing changed wrote something"
$DIFF -- "$TMP_DIR/env.before" .lake/paperlean/env.json || fail "a prepare with nothing changed changed env.json"
