# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that plain `lake` of PaperLean gives a module's setup as official Lake does: `lake build` writes
# `.setup.json` pretty-printed (`Lake.compileLeanModule`), with `importArts` in full paths, and `lake
# query` and `lake setup-file` give the same `importArts`; only the Lake of the `paperlean` commands
# (`PAPERLEAN_ACCELERATE=1`) writes it compact, with `importArts` referring to the build's setup
# index (`Lake.PaperLean.SetupIndex`), which official Lean does not read, in a side file.

WS="$(cd "$TMP_DIR" && pwd -P)/ws"
mkdir -p "$WS/R"
cd "$WS"
cat > lakefile.toml <<'END'
name = "r"
defaultTargets = ["R"]
[[lean_lib]]
name = "R"
END
echo 'def a : Nat := 1' > R/A.lean
printf 'import R.A\ndef b : Nat := a + 1\n' > R.lean
cat > "$TMP_DIR/show.lean" <<'END'
import Lean.Data.Json
open Lean
-- the JSON on the standard input as `Json.pretty` prints it, or its `importArts` as one line
def main (args : List String) : IO UInt32 := do
  let .ok val := Json.parse (← (← IO.getStdin).readToEnd) | return 1
  if args == ["arts"] then IO.println (val.getObjValD "importArts").compress else IO.print val.pretty
  return 0
END
show_json() { lake env lean --run "$TMP_DIR/show.lean" "$@"; }
FULL="{\"R.A\":[[\"$WS/.lake/build/lib/lean/R/A.olean\"]]}"
SETUP=.lake/build/ir/R.setup.json
run lake build
for m in R R/A; do
  show_json < .lake/build/ir/$m.setup.json > "$TMP_DIR/pretty.json"
  cmp .lake/build/ir/$m.setup.json "$TMP_DIR/pretty.json" || fail "plain lake build did not write $m.setup.json as Json.pretty"
done
[ "$(show_json arts < $SETUP)" = "$FULL" ] || fail "plain lake build wrote importArts as: $(show_json arts < $SETUP)"
[ "$(lake query +R:setup --json | show_json arts)" = "$FULL" ] || fail "lake query gave another importArts"
[ "$(lake setup-file R.lean | show_json arts)" = "$FULL" ] || fail "lake setup-file gave another importArts"
echo '-- changed' >> R.lean
run env PAPERLEAN_ACCELERATE=1 lake build
SIDE=.lake/build/ir/R.setup.paperlean
[ "$(wc -l < $SIDE)" -eq 0 ] || fail "the Lake of paperlean commands did not write R.setup.paperlean compact"
INDEX="$WS/\\.lake/paperlean-setup/[0-9]+-[0-9]+/setup-[0-9a-f]+\\.paperlean"
show_json arts < $SIDE | grep -Eq "^\\{\"\\[anonymous\\]\":\\[\\[\"$INDEX\"\\],\\[\"[0-9]+\"\\]\\]\\}$" ||
  fail "the Lake of paperlean commands wrote importArts as: $(show_json arts < $SIDE)"
[ "$(show_json arts < $SETUP)" = "$FULL" ] || fail "the Lake of paperlean commands changed R.setup.json: $(show_json arts < $SETUP)"
echo '-- changed again' >> R.lean
run lake build
[ "$(show_json arts < $SETUP)" = "$FULL" ] || fail "plain lake build after one of a paperlean command wrote importArts as: $(show_json arts < $SETUP)"
