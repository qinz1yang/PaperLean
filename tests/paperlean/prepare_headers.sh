# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests the parsed source headers reused by prepare: an unchanged run keeps them, source edits
# invalidate them even with the old mtime, and damaged cache data falls back to parsing. A preflight
# failure leaves env.json and the header cache unchanged.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN PAPERLEAN_DATA
ROOT="$(cd "$TMP_DIR" && pwd -P)"
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
capture lake paperlean prepare --no-native
check_out_contains "Prepared"
HEADERS=.lake/paperlean/imports.paperlean
[ -s "$HEADERS" ] || fail "prepare did not save parsed source headers"
cp "$HEADERS" "$TMP_DIR/headers.before"
cp .lake/paperlean/env.json "$TMP_DIR/env.before"
cp -p Root.lean "$TMP_DIR/root.before"
cp -p ../dep/Dep/A.lean "$TMP_DIR/a.before"

# An unchanged prepare neither changes the cached headers nor the prepared environment.
capture lake paperlean prepare --no-native
$DIFF -- "$TMP_DIR/headers.before" "$HEADERS" || fail "unchanged source headers were rewritten"
$DIFF -- "$TMP_DIR/env.before" .lake/paperlean/env.json || fail "unchanged prepare changed env.json"

# Root-source invalidation must use ctime as well as the modification time and file size.
printf 'import Dep.B\n#eval aValue\n' > Root.lean
touch -r "$TMP_DIR/root.before" Root.lean
capture_exit 1 lake paperlean prepare --no-native
check_out_contains "Dep.B"
check_out_contains "Nothing was changed"
$DIFF -- "$TMP_DIR/env.before" .lake/paperlean/env.json || fail "failed prepare changed env.json"
$DIFF -- "$TMP_DIR/headers.before" "$HEADERS" || fail "failed prepare changed the header cache"
cp -p "$TMP_DIR/root.before" Root.lean

# The same check applies to headers of dependency modules, including a changed header with the old mtime.
printf 'import Dep.B\ndef aValue : Nat := 42\n' > ../dep/Dep/A.lean
touch -r "$TMP_DIR/a.before" ../dep/Dep/A.lean
capture_exit 1 lake paperlean prepare --no-native
check_out_contains "Dep.B"
$DIFF -- "$TMP_DIR/env.before" .lake/paperlean/env.json || fail "failed prepare changed env.json"
$DIFF -- "$TMP_DIR/headers.before" "$HEADERS" || fail "failed prepare changed the header cache"
cp -p "$TMP_DIR/a.before" ../dep/Dep/A.lean

# Corrupt metadata is optional: prepare rebuilds it without changing its normal result.
printf '{ damaged\n' > "$HEADERS"
capture lake paperlean prepare --no-native
check_out_contains "Prepared"
[ -s "$HEADERS" ] || fail "prepare did not repair corrupt cached headers"
! grep -q 'damaged' "$HEADERS" || fail "prepare kept corrupt cached headers"
capture env PAPERLEAN_ACCELERATE=1 lake lean Root.lean
check_out_contains "42"
