# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests `paperlean prepare` of two workspaces with the same dependency at the same time: the entries
# of the cache are written once (the other run waits for the lock of an entry and then uses it), no
# temporary files stay, and both workspaces get the same results as without prepared data.

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
for i in $(seq 1 12); do echo "def d$i (n : Nat) : Nat := n + $i" > dep/Dep/M$i.lean; echo "import Dep.M$i" >> dep/Dep.lean; done
cat > dep/Dep/Twice.lean <<'END'
import Lean
macro "twice! " x:term : term => `($x + $x)
END
echo 'import Dep.Twice' >> dep/Dep.lean
cat > lakefile.toml <<'END'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "dep"
path = "dep"
[[lean_lib]]
name = "Root"
END
printf 'import Dep\n#eval twice! d3 20\n' > Root.lean
run lake build Dep
capture lake lean Root.lean
cp "$CAPTURED.out.produced" "$TMP_DIR/plain.out"
cp -pR "$ROOT/ws1" "$ROOT/ws2"

for w in ws1 ws2; do
  (cd "$ROOT/$w" && { lake paperlean prepare -j 2 > "$TMP_DIR/$w.out" 2>&1; echo $? > "$TMP_DIR/$w.code"; }) &
done
wait
for w in ws1 ws2; do
  [ "$(cat "$TMP_DIR/$w.code")" = 0 ] || fail "prepare in $w failed: $(cat "$TMP_DIR/$w.out")"
  grep -q "^Prepared" "$TMP_DIR/$w.out" || fail "prepare in $w did not finish: $(cat "$TMP_DIR/$w.out")"
done
[ "$(cat "$TMP_DIR"/ws1.out "$TMP_DIR"/ws2.out | grep -c "^Packing dep")" = 1 ] ||
  fail "dep was not packed once: $(cat "$TMP_DIR"/ws1.out "$TMP_DIR"/ws2.out)"
[ "$(cat "$TMP_DIR"/ws1.out "$TMP_DIR"/ws2.out | grep -c "^Compiling the native library of dep")" = 1 ] ||
  fail "dep's library was not compiled once: $(cat "$TMP_DIR"/ws1.out "$TMP_DIR"/ws2.out)"
[ "$(ls -d "$CACHE"/*/pack/dep-* | wc -l | tr -d ' ')" = 1 ] || fail "not one pack of dep: $(ls -a "$CACHE"/*/pack)"
[ "$(ls -d "$CACHE"/*/native/dep-* | wc -l | tr -d ' ')" = 1 ] || fail "not one library of dep: $(ls -a "$CACHE"/*/native)"
ls -d "$CACHE"/*/pack/.tmp-* "$CACHE"/*/native/.tmp-* "$CACHE"/*/objects/*.tmp.* 2> /dev/null &&
  fail "temporary files were left"
for w in ws1 ws2; do
  cd "$ROOT/$w"
  capture env PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean Root.lean
  check_out_matches "paperlean-timing native libs=1 "
  { grep -v "^paperlean-" "$CAPTURED.out.produced" || true; } | $DIFF -- "$TMP_DIR/plain.out" - ||
    fail "the prepared data changes the output in $w"
done
