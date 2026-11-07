# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Prepare reuses only source facts from the user's cache. A project-local record
# must never choose dependencies; failed preflights leave published state intact.
unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN PAPERLEAN_DATA
ROOT="$(cd "$TMP_DIR" && pwd -P)"
export PAPERLEAN_CACHE_DIR="$ROOT/cache" PAPERLEAN_SOURCE_INPUT_CACHE=1
cp "$TEST_DIR/paperlean/prepare_header_probe.lean" "$ROOT/Probe.lean"
run lean --root="$ROOT" --c="$ROOT/probe.c" "$ROOT/Probe.lean"
link=(-lLake_shared -leanshared -lleanshared)
if [[ "$OSTYPE" != "cygwin" && "$OSTYPE" != "msys" ]]; then
  link+=(-Wl,-rpath,"$BUILD_DIR/lib/lean")
fi
run leanc ${LEANC_OPTS-} -O2 -o "$ROOT/probe" "$ROOT/probe.c" "${link[@]}"

mkdir -p "$ROOT/dep/Dep" "$ROOT/ws"
cat > "$ROOT/dep/lakefile.toml" <<'END'
name = "dep"
defaultTargets = ["Dep"]
[[lean_lib]]
name = "Dep"
END
printf 'import Dep.C\ndef aValue : Nat := 42\n' > "$ROOT/dep/Dep/A.lean"
printf 'def aValue : Nat := 1\n' > "$ROOT/dep/Dep/B.lean"
printf 'def cValue : Nat := 3\n' > "$ROOT/dep/Dep/C.lean"
printf 'import Dep.A\n' > "$ROOT/dep/Dep.lean"
cat > "$ROOT/ws/lakefile.toml" <<'END'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "dep"
path = "../dep"
[[lean_lib]]
name = "Root"
END
printf 'import Dep.A\n#eval aValue\n' > "$ROOT/ws/Root.lean"
cd "$ROOT/ws"
run lake build Dep.A
sleep 3 # the cache admits only files older than its coarse-clock safety margin
LEGACY=.lake/paperlean/imports.paperlean
mkdir -p .lake/paperlean
run "$ROOT/probe" forge "$LEGACY" Root.lean
cp "$LEGACY" "$TMP_DIR/legacy.before"
capture lake paperlean prepare --no-native
check_out_contains "Prepared"
$DIFF -- "$TMP_DIR/legacy.before" "$LEGACY" || fail "prepare changed the legacy record"
HEADERS="$("$ROOT/probe" cache "$PWD")"
cached="$("$ROOT/probe" supported "$PWD/Root.lean")"
if [ "$cached" = true ]; then
  [ -s "$HEADERS" ] || fail "prepare did not save verified user-cache headers"
  cp "$HEADERS" "$TMP_DIR/headers.before"
fi
cp .lake/paperlean/env.json "$TMP_DIR/env.before"
cp -p Root.lean "$TMP_DIR/root.before"
cp -p ../dep/Dep/A.lean "$TMP_DIR/a.before"

# An unchanged prepare neither changes the cached headers nor the prepared environment.
capture env PAPERLEAN_SOURCE_INPUT_STATS=1 lake paperlean prepare --no-native
if [ "$cached" = true ]; then
  check_out_matches 'PaperLean source inputs: hits=[1-9][0-9]* new=0'
  $DIFF -- "$TMP_DIR/headers.before" "$HEADERS" || fail "unchanged source headers were rewritten"
fi
$DIFF -- "$TMP_DIR/env.before" .lake/paperlean/env.json || fail "unchanged prepare changed env.json"

# Root-source invalidation must use ctime as well as the modification time and file size.
printf 'import Dep.B\n#eval aValue\n' > Root.lean
touch -r "$TMP_DIR/root.before" Root.lean
capture_exit 1 lake paperlean prepare --no-native
check_out_contains "Dep.B"
check_out_contains "Nothing was changed"
$DIFF -- "$TMP_DIR/env.before" .lake/paperlean/env.json || fail "failed prepare changed env.json"
[ "$cached" != true ] || $DIFF -- "$TMP_DIR/headers.before" "$HEADERS" || fail "failed prepare changed the header cache"
cp -p "$TMP_DIR/root.before" Root.lean

# The same check applies to headers of dependency modules, including a changed header with the old mtime.
printf 'import Dep.B\ndef aValue : Nat := 42\n' > ../dep/Dep/A.lean
touch -r "$TMP_DIR/a.before" ../dep/Dep/A.lean
capture_exit 1 lake paperlean prepare --no-native
check_out_contains "Dep.B"
$DIFF -- "$TMP_DIR/env.before" .lake/paperlean/env.json || fail "failed prepare changed env.json"
[ "$cached" != true ] || $DIFF -- "$TMP_DIR/headers.before" "$HEADERS" || fail "failed prepare changed the header cache"
cp -p "$TMP_DIR/a.before" ../dep/Dep/A.lean

# Legacy metadata may even be a FIFO: no reader waits on it. Verify this under a deadline.
if [[ "$OSTYPE" != "cygwin" && "$OSTYPE" != "msys" ]]; then
  rm "$LEGACY"
  mkfifo "$LEGACY"
  run python3 -c 'import subprocess; subprocess.run(["lake","paperlean","prepare","--no-native"],timeout=60,check=True)'
  [ -p "$LEGACY" ] || fail "prepare touched the legacy FIFO"
  rm "$LEGACY"
fi

# Corrupt user-cache metadata falls back to the parser and is repaired after success.
if [ "$cached" = true ]; then
  printf '{ damaged\n' > "$HEADERS"
fi
capture lake paperlean prepare --no-native
check_out_contains "Prepared"
if [ "$cached" = true ]; then
  [ -s "$HEADERS" ] || fail "prepare did not repair corrupt cached headers"
  ! cmp -s "$HEADERS" <(printf '{ damaged\n') || fail "prepare kept corrupt source data"
fi
$DIFF -- "$TMP_DIR/env.before" .lake/paperlean/env.json || fail "corrupt inputs changed prepared data"
capture env PAPERLEAN_ACCELERATE=1 lake lean Root.lean
check_out_contains "42"

# The old predictable intermediate paths must neither be opened nor removed.
mkdir -p "$ROOT/events"
printf external > "$ROOT/external"
run env PAPERLEAN_NATIVE_REPAIR_EVENTS="$ROOT/events" "$ROOT/probe" event "$ROOT/events" "$ROOT/external"
if image=$(python3 -c 'import json; value=json.load(open(".lake/paperlean/env.json")).get("image"); print(value or "")') && [ -n "$image" ]; then
  run "$ROOT/probe" image .lake/paperlean "$ROOT/external" "$image"
  if [[ "$OSTYPE" != "cygwin" && "$OSTYPE" != "msys" ]]; then
    receipt=".lake/paperlean/$image.checked.json"
    mv "$receipt" "$receipt.saved"
    mkfifo "$receipt"
    run python3 -c 'import subprocess,sys;subprocess.run(sys.argv[1:],timeout=10,check=True)' \
      "$ROOT/probe" receipt .lake/paperlean "$image"
    rm "$receipt"
    mv "$receipt.saved" "$receipt"
  fi
fi
