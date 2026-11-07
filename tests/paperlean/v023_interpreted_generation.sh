# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
cat >"$TMP_DIR/GenerationObserver.lean" <<'LEAN'
import Lake.PaperLean.Env

initialize observed : Unit ← do
  let some path ← IO.getEnv "PAPERLEAN_TEST_GENERATION" | return ()
  IO.FS.writeFile path (toString (← Lake.PaperLean.freshGeneration))
LEAN
cat >"$TMP_DIR/GenerationDriver.lean" <<'LEAN'
import Lean.Environment
import Lake.PaperLean.Env

def main (args : List String) : IO Unit := do
  let [observer] := args | throw <| IO.userError "expected observer plugin"
  let some path ← IO.getEnv "PAPERLEAN_TEST_GENERATION" | throw <| IO.userError "missing observation path"
  let outer ← Lake.PaperLean.freshGeneration
  Lean.withImporting <| Lean.loadPlugin observer (some "initialize_GenerationObserver")
  let some inner := (← IO.FS.readFile path).toNat? | throw <| IO.userError "invalid observation"
  unless inner > outer do
    throw <| IO.userError s!"native generation {inner} reused interpreted generation {outer}"
LEAN
run lean --root="$TMP_DIR" --c="$TMP_DIR/GenerationObserver.c" "$TMP_DIR/GenerationObserver.lean"
if [[ "$OSTYPE" == darwin* ]]; then
  ext=dylib
else
  ext=so
fi
observer="$TMP_DIR/observer.$ext"
libDir="$(lean --print-prefix)/lib/lean"
observerLinkFlags=()
if [[ "$OSTYPE" == linux* ]]; then
  observerLinkFlags=(-Wl,--enable-new-dtags -Xlinker -rpath -Xlinker "$libDir")
fi
run leanc ${LEANC_OPTS-} -shared -fPIC -DLEAN_EXPORTING -o "$observer" "$TMP_DIR/GenerationObserver.c" -lLake_shared "${observerLinkFlags[@]}"
lakeLib="$libDir/libLake_shared.$ext"
for mode in late early; do
  rm -f "$TMP_DIR/$mode.observed"
  flags=()
  if [[ $mode == early ]]; then flags+=("--plugin=$lakeLib=initialize_Lake"); fi
  run env PAPERLEAN_TEST_GENERATION="$TMP_DIR/$mode.observed" \
    lean "${flags[@]}" --run "$TMP_DIR/GenerationDriver.lean" "$observer"
done
