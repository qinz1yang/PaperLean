# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests the setup index of `paperlean build` (`Lake.PaperLean.SetupIndex`): the setup of each module
# that the build compiles refers to a record of the build's index instead of listing the artifacts of
# the module's transitive imports, and `ModuleSetup.load` computes from the index exactly the
# artifacts that `lake build` lists, here for `module`s and files that are none, with `import all`,
# `meta` and private imports, across two packages; the build compiles what `lake build` does. A stray
# `.olean` of a module that the search path finds before the module's own is not read. A setup whose
# index is missing or damaged fails the module's `lean`, saying so.

export XDG_CACHE_HOME="$(cd "$TMP_DIR" && pwd -P)/cache"
WS="$(cd "$TMP_DIR" && pwd -P)/ws"
DEP="$(cd "$TMP_DIR" && pwd -P)/d"
mkdir -p "$WS/R" "$DEP/D"
cat > "$DEP/lakefile.toml" <<'END'
name = "d"
defaultTargets = ["D"]
[[lean_lib]]
name = "D"
END
printf 'module\npublic def a : Nat := 1\n' > "$DEP/D/A.lean"
printf 'module\npublic import D.A\npublic def b : Nat := a + 1\n' > "$DEP/D/B.lean"
printf 'def p : Nat := 7\n' > "$DEP/D/P.lean"
printf 'import D.B\nimport D.P\n' > "$DEP/D.lean"
cd "$WS"
cat > lakefile.toml <<'END'
name = "r"
defaultTargets = ["R"]
[[require]]
name = "d"
path = "../d"
[[lean_lib]]
name = "R"
END
printf 'module\npublic def base : Nat := 10\ndef secret : Nat := 3\n' > R/Base.lean
printf 'module\npublic import R.Base\nimport D.A\npublic def mid : Nat := base + 1\n' > R/Mid.lean
printf 'module\nimport all R.Base\ndef useSecret : Nat := secret\n' > R/AllUser.lean
printf 'module\nmeta import R.Mid\n' > R/MetaUser.lean
printf 'module\npublic import R.Mid\nimport all R.AllUser\nmeta import R.MetaUser\nimport D.B\npublic def top : Nat := mid + 1\n' > R/Top.lean
printf 'def plain : Nat := 1\n' > R/Plain.lean
printf 'import R.Plain\nexample : plain = 1 := rfl\n' > R/UsesPlain.lean
printf 'import R.Top\nimport D.P\ndef legacy : Nat := top + p\n' > R/Legacy.lean
printf 'import R.Legacy\nimport R.UsesPlain\n' > R.lean
MODS="R R.Base R.Mid R.AllUser R.MetaUser R.Top R.Plain R.UsesPlain R.Legacy D.A D.B D.P"
setup_file() { # the side file of module `$1`
  case "$1" in
    D.*) echo "$DEP/.lake/build/ir/$(echo "$1" | tr . /).setup.paperlean" ;;
    *) echo "$WS/.lake/build/ir/$(echo "$1" | tr . /).setup.paperlean" ;;
  esac
}
cat > "$TMP_DIR/arts.lean" <<'END'
import Lean.Setup
open Lean
-- `importArts` of the setup JSON on the standard input, or its keys, or as `ModuleSetup.load` reads
-- file `$1`
def main (args : List String) : IO UInt32 := do
  match args with
  | ["keys"] =>
    let .ok (Json.obj o) := (Json.parse (← (← IO.getStdin).readToEnd)).map (·.getObjValD "importArts")
      | return 1
    IO.println (" ".intercalate o.keys)
  | [file] => IO.println (toJson (← ModuleSetup.load file).importArts).compress
  | _ =>
    let .ok val := Json.parse (← (← IO.getStdin).readToEnd) | return 1
    IO.println (val.getObjValD "importArts").compress
  return 0
END
arts() { lake env lean --run "$TMP_DIR/arts.lean" "$@"; }
outputs() { find .lake/build "$DEP/.lake/build" -name '*.olean*' -o -name '*.ilean' -o -name '*.c' -o -name '*.ir*' -o -name '*.trace' | sort; }

# What `lake build` compiles, and the artifacts it lists.
run lake build
outputs > "$TMP_DIR/outputs"
while read -r f; do mkdir -p "$TMP_DIR/ref/$(dirname "$f")"; cp "$f" "$TMP_DIR/ref/$f"; done < "$TMP_DIR/outputs"
for m in $MODS; do lake query "+$m:setup" --json | arts > "$TMP_DIR/$m.arts"; done
grep -q 'olean.private' "$TMP_DIR/R.Top.arts" || fail "the test does not test this: no import all in R.Top"

# A stray `R/Plain.olean` where the search path looks first, in the dependency's library directory.
lib_dirs="$(lake env printenv LEAN_PATH)"
[ "${lib_dirs%%:*}" = "$DEP/.lake/build/lib/lean" ] || fail "the test does not test this: LEAN_PATH is $lib_dirs"
mkdir -p "$TMP_DIR/stray/R"
printf 'name = "s"\n[[lean_lib]]\nname = "R"\n' > "$TMP_DIR/stray/lakefile.toml"
printf 'def plain : Nat := 2\n' > "$TMP_DIR/stray/R/Plain.lean"
(cd "$TMP_DIR/stray" && lake build R.Plain) > /dev/null || fail "no stray olean"
rm -rf .lake/build "$DEP/.lake/build"
mkdir -p "$DEP/.lake/build/lib/lean/R"
cp "$TMP_DIR/stray/.lake/build/lib/lean/R/Plain.olean" "$DEP/.lake/build/lib/lean/R/"

# `paperlean build` compiles the same files.
capture env PAPERLEAN_SETUP_INDEX_KEEP=1 lake paperlean build
while read -r f; do cmp -s "$f" "$TMP_DIR/ref/$f" || fail "$f differs from plain lake's"; done < "$TMP_DIR/outputs"
# (which the stray would change: `lean` reads it when it searches, as here with `lake env`)
echo 'import R.Plain
#eval plain' > "$TMP_DIR/probe.lean"
capture lake env lean "$TMP_DIR/probe.lean"
check_out_contains 2
[ ! -e .lake/build/ir/R/Top.setup.json ] || fail "paperlean build wrote the conventional setup file"
indexes="$(ls .lake/paperlean-setup/*/setup-*.paperlean)"
[ "$(echo "$indexes" | wc -l)" = 1 ] || fail "not one index: $indexes"
# Each setup refers to the index, and `ModuleSetup.load` gives the artifacts that `lake build` lists.
for m in $MODS; do
  side="$(setup_file "$m")"
  [ "$(arts keys < "$side")" = "[anonymous]" ] ||
    fail "the setup of $m does not refer to the index only: $(cat "$side")"
  grep -q "$indexes" "$side" || fail "the setup of $m does not refer to $indexes"
  [ "$(arts "$side")" = "$(cat "$TMP_DIR/$m.arts")" ] ||
    fail "the artifacts of the imports of $m differ: $(arts "$side") vs. $(cat "$TMP_DIR/$m.arts")"
done

# A missing or damaged index fails `lean`.
side="$(setup_file R.Top)"
cp "$indexes" "$TMP_DIR/index"
echo x >> "$indexes"
capture_fail lake env lean --setup "$side" R/Top.lean
check_out_contains "is damaged: its contents do not have the hash it is named by"
rm "$indexes"
capture_fail lake env lean --setup "$side" R/Top.lean
check_out_contains "cannot be read"
# (and the index as written passes)
cp "$TMP_DIR/index" "$indexes"
capture lake env lean --setup "$side" R/Top.lean

# Without the variable for tests, the build removes its index.
echo '-- changed' >> R/Top.lean
capture lake paperlean build
[ -z "$(ls .lake/paperlean-setup/*/setup-*.paperlean 2>/dev/null | grep -v "$indexes")" ] ||
  fail "the build left its index: $(ls .lake/paperlean-setup/*)"
capture_fail lake env lean --setup "$side" R/Top.lean
