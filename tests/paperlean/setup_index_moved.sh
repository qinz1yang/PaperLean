# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests the setup index of `paperlean build` (`Lake.PaperLean.SetupIndex`) with artifacts elsewhere
# than in the source directories of their packages: those of a path dependency that Lake copies
# (`copy = true`), where the index has them, and not the source's own build; and those in Lake's
# artifact cache, which the setups of their importers list. Each build compiles what `lake build` does,
# and `ModuleSetup.load` gives the artifacts that `lake build` lists.

export XDG_CACHE_HOME="$(cd "$TMP_DIR" && pwd -P)/cache"
# (the indexes are kept for `ModuleSetup.load` after the builds)
export PAPERLEAN_SETUP_INDEX_KEEP=1
WS="$(cd "$TMP_DIR" && pwd -P)/ws"
mkdir -p "$WS/foo/Foo" "$WS/R"
cd "$WS"
cat > foo/lakefile.toml <<'END'
name = "foo"
defaultTargets = ["Foo"]
[[lean_lib]]
name = "Foo"
END
printf 'module\npublic def x : Nat := 1\n' > foo/Foo/X.lean
printf 'module\npublic import Foo.X\n' > foo/Foo.lean
cat > lakefile.toml <<'END'
name = "r"
defaultTargets = ["R"]
[[require]]
name = "foo"
path = "foo"
copy = true
[[lean_lib]]
name = "R"
END
printf 'module\nimport all Foo.X\npublic def y : Nat := x + 1\n' > R/Y.lean
printf 'import R.Y\nexample : y = 2 := by decide\n' > R/Z.lean
printf 'import R.Z\n' > R.lean
cat > "$TMP_DIR/arts.lean" <<'END'
import Lean.Setup
open Lean
-- `importArts` of the setup JSON on the standard input, or as `ModuleSetup.load` reads file `$1`
def main (args : List String) : IO UInt32 := do
  match args with
  | [file] => IO.println (toJson (← ModuleSetup.load file).importArts).compress
  | _ =>
    let .ok val := Json.parse (← (← IO.getStdin).readToEnd) | return 1
    IO.println (val.getObjValD "importArts").compress
  return 0
END
arts() { lake env lean --run "$TMP_DIR/arts.lean" "$@"; }
# The artifacts of the imports of `$1` that `lake build` lists are those that `ModuleSetup.load` gives.
same_arts() {
  local side=".lake/build/ir/$(echo "$1" | tr . /).setup.paperlean"
  [ "$(lake query "+$1:setup" --json | arts)" = "$(arts "$side")" ] ||
    fail "the artifacts of the imports of $1 differ: $(lake query "+$1:setup" --json | arts) vs. $(arts "$side")"
}
outputs() { find .lake/build .lake/packages/foo/.lake/build -name '*.olean*' -o -name '*.ilean' -o -name '*.c' -o -name '*.ir*' | sort; }

run lake build
outputs > "$TMP_DIR/outputs"
while read -r f; do mkdir -p "$TMP_DIR/ref/$(dirname "$f")"; cp "$f" "$TMP_DIR/ref/$f"; done < "$TMP_DIR/outputs"
[ -f .lake/packages/foo/.lake/build/lib/lean/Foo/X.olean ] || fail "the test does not test this: foo is not built in its copy"

# The source of the copied dependency has a build of its own, of another `x`.
printf 'module\npublic def x : Nat := 5\n' > foo/Foo/X.lean
(cd foo && lake build) > /dev/null || fail "foo did not build in place"
rm -rf .lake/build .lake/packages/foo/.lake/build
capture lake paperlean build
while read -r f; do cmp -s "$f" "$TMP_DIR/ref/$f" || fail "$f differs from plain lake's"; done < "$TMP_DIR/outputs"
grep -q "$WS/.lake/packages/foo/.lake/build/lib/lean" .lake/paperlean-setup/*/setup-*.paperlean &&
  ! grep -q "$WS/foo/.lake" .lake/paperlean-setup/*/setup-*.paperlean ||
  fail "the index does not have the library directory of the copy"
for m in R R.Y R.Z; do same_arts $m; done

# Lake's artifact cache, from which it gives artifacts without copying them to the build directory.
export LAKE_ARTIFACT_CACHE=true LAKE_CACHE_DIR="$TMP_DIR/lakecache"
rm -rf .lake/build .lake/packages/foo/.lake/build
capture lake paperlean build
while read -r f; do cmp -s "$f" "$TMP_DIR/ref/$f" || fail "$f differs from plain lake's"; done < "$TMP_DIR/outputs"
grep -q "$LAKE_CACHE_DIR" .lake/build/ir/R/Z.setup.paperlean ||
  fail "the setup of R.Z does not list the artifacts in the cache: $(cat .lake/build/ir/R/Z.setup.paperlean)"
for m in R R.Y R.Z; do same_arts $m; done
# Only the changed module compiles, with its imports in the cache.
rm -rf .lake/build .lake/packages/foo/.lake/build
echo '-- changed' >> R/Z.lean
capture lake paperlean build
check_out_contains "Built R.Z"
[ ! -f .lake/build/lib/lean/R/Y.olean ] || fail "the test does not test this: R.Y was restored to the build directory"
same_arts R.Z
