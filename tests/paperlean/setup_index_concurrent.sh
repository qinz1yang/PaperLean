# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests two `paperlean build`s that run at the same time in one workspace: each has its own setup index
# (`Lake.PaperLean.SetupIndex`), which the other does not remove when it ends: the second one starts
# while the first compiles a module, and ends before the first compiles the next, which imports it;
# both compile what `lake build` does, and remove their indexes.

export XDG_CACHE_HOME="$(cd "$TMP_DIR" && pwd -P)/cache"
WS="$(cd "$TMP_DIR" && pwd -P)/ws"
MARK="$TMP_DIR/compiling"
mkdir -p "$WS/Slow" "$WS/Fast"
cd "$WS"
cat > lakefile.toml <<'END'
name = "w"
defaultTargets = ["Slow", "Fast"]
[[lean_lib]]
name = "Common"
[[lean_lib]]
name = "Slow"
[[lean_lib]]
name = "Fast"
END
echo 'def common : Nat := 1' > Common.lean
# (with `SLOW` set, waits until the test removes the mark, but not for ever)
cat > Slow/A.lean <<END
import Common
#eval show IO Unit from do
  if (← IO.getEnv "SLOW").isNone then return
  IO.FS.writeFile "$MARK" ""
  for _ in [0:600] do
    unless ← System.FilePath.pathExists "$MARK" do return
    IO.sleep 100
def slow : Nat := common + 1
END
printf 'import Slow.A\ndef slow2 : Nat := slow + 1\n' > Slow/B.lean
printf 'import Slow.B\n' > Slow.lean
printf 'import Common\ndef fast : Nat := common + 2\n' > Fast/A.lean
printf 'import Fast.A\n' > Fast.lean
outputs() { find .lake/build -name '*.olean*' -o -name '*.ilean' -o -name '*.c' | sort; }

run lake build
outputs > "$TMP_DIR/outputs"
while read -r f; do mkdir -p "$TMP_DIR/ref/$(dirname "$f")"; cp "$f" "$TMP_DIR/ref/$f"; done < "$TMP_DIR/outputs"
rm -rf .lake/build/lib/lean/Slow* .lake/build/lib/lean/Fast* .lake/build/ir/Slow* .lake/build/ir/Fast*

SLOW=1 lake paperlean build Slow > "$TMP_DIR/slow.out" 2>&1 &
slow=$!
for _ in $(seq 600); do [ -e "$MARK" ] && break; sleep 0.1; done
[ -e "$MARK" ] || { cat "$TMP_DIR/slow.out"; fail "Slow.A did not start compiling"; }
indexes="$(ls .lake/paperlean-setup/*/setup-*.paperlean)"
[ "$(echo "$indexes" | wc -l)" -eq 1 ] || fail "not the index of the first build: $indexes"
capture lake paperlean build Fast
check_out_contains "Built Fast.A"
[ -f "$indexes" ] || fail "the second build removed the index of the first"
rm "$MARK"
wait $slow || { cat "$TMP_DIR/slow.out"; fail "the first build failed"; }
cat "$TMP_DIR/slow.out"
grep -q "Built Slow.B" "$TMP_DIR/slow.out" || fail "the first build did not compile Slow.B"
while read -r f; do cmp -s "$f" "$TMP_DIR/ref/$f" || fail "$f differs from plain lake's"; done < "$TMP_DIR/outputs"
[ -z "$(ls .lake/paperlean-setup/*/setup-*.paperlean 2>/dev/null)" ] ||
  fail "the builds left indexes: $(ls .lake/paperlean-setup/*)"
