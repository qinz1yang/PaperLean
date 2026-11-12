# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that prepared-data replacement and cleanup must not
# follow a symbolic link at env.json, bind/, or a root-<stamp>/ directory.
# Run from tests/paperlean (sourced by run_test.sh) or directly with `bash`.
if [ -z "${TMP_DIR:-}" ]; then
  TMP_DIR="$(mktemp -d)"
  trap 'rm -rf "$TMP_DIR"' EXIT
fi
# (run_test.sh defines `fail`; a direct run does not)
if ! declare -F fail > /dev/null; then
  fail() { echo "TEST FAILED: $1"; exit 1; }
fi
if [ -z "${PAPERLEAN_CACHE_DIR:-}" ]; then
  export PAPERLEAN_CACHE_DIR="$TMP_DIR/cache"
fi
unset PAPERLEAN_ACCELERATE PAPERLEAN_DATA LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS ELAN_TOOLCHAIN 2>/dev/null || true
WS="$TMP_DIR/ws"
mkdir -p "$WS/dep/Dep"
cd "$WS"
cat > dep/lakefile.toml <<'END'
name = "dep"
defaultTargets = ["Dep"]
[[lean_lib]]
name = "Dep"
END
printf 'def base (n : Nat) : Nat := n + 1\n' > dep/Dep.lean
cat > lakefile.toml <<'END'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "dep"
path = "dep"
[[lean_lib]]
name = "Root"
END
printf 'import Dep\n#eval base 41\n' > Root.lean
lake build > "$TMP_DIR/build.log" 2>&1 || fail "the initial build failed"
lake paperlean prepare --no-native -j 2 > "$TMP_DIR/prepare.log" 2>&1 || fail "the initial prepare failed"
cp .lake/paperlean/env.json "$TMP_DIR/env.json"

# 1. env.json is a symbolic link to a directory outside the data directory.
mkdir -p "$TMP_DIR/victim-env"
echo keep > "$TMP_DIR/victim-env/keep.txt"
rm -f .lake/paperlean/env.json
ln -s "$TMP_DIR/victim-env" .lake/paperlean/env.json
lake paperlean prepare --no-native -j 2 > "$TMP_DIR/env-link.log" 2>&1 ||
  fail "prepare failed with an env.json link: $(cat "$TMP_DIR/env-link.log")"
[ -f "$TMP_DIR/victim-env/keep.txt" ] ||
  fail "prepare followed the env.json link and deleted $TMP_DIR/victim-env/keep.txt"
[ -f .lake/paperlean/env.json ] && [ ! -L .lake/paperlean/env.json ] ||
  fail "prepare did not replace the env.json link with its file"
rm -f .lake/paperlean/env.json
cp "$TMP_DIR/env.json" .lake/paperlean/env.json

# 2. bind/ is a symbolic link to a directory outside the data directory.
mkdir -p "$TMP_DIR/victim-bind"
echo keep > "$TMP_DIR/victim-bind/keep.txt"
rm -rf .lake/paperlean/bind
ln -s "$TMP_DIR/victim-bind" .lake/paperlean/bind
lake paperlean prepare --no-native -j 2 > "$TMP_DIR/bind-link.log" 2>&1 ||
  fail "prepare failed with a bind/ link: $(cat "$TMP_DIR/bind-link.log")"
[ -f "$TMP_DIR/victim-bind/keep.txt" ] ||
  fail "prepare followed the bind/ link and deleted $TMP_DIR/victim-bind/keep.txt"
[ -z "$(ls "$TMP_DIR/victim-bind"/dep-*.paperlean 2>/dev/null || true)" ] ||
  fail "prepare wrote a binding through the bind/ link"
[ -d .lake/paperlean/bind ] && [ ! -L .lake/paperlean/bind ] ||
  fail "prepare did not replace the bind/ link with a real directory"

# 3. a root-<stamp>/ directory is a symbolic link; refresh must not write into it.
lake paperlean prepare --no-native --all -j 2 > "$TMP_DIR/prepare-all.log" 2>&1 ||
  fail "prepare --all failed: $(cat "$TMP_DIR/prepare-all.log")"
ROOTDIR=$(python3 - .lake/paperlean/env.json <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
p = next((p for p in d.get('packs', []) if p.endswith('/root.paperlean')), None)
if not p:
    raise SystemExit('no root pack')
print(p.split('/')[0])
PY
)
[ -n "$ROOTDIR" ] || fail "no root pack directory"
mkdir -p "$TMP_DIR/victim-root"
echo keep > "$TMP_DIR/victim-root/keep.txt"
cp ".lake/paperlean/$ROOTDIR/root.paperlean" "$TMP_DIR/victim-root/root.paperlean"
rm -rf ".lake/paperlean/$ROOTDIR"
ln -s "$TMP_DIR/victim-root" ".lake/paperlean/$ROOTDIR"
printf '\n-- changed\n' >> Root.lean
lake paperlean build --prepare > "$TMP_DIR/refresh-link.log" 2>&1 ||
  fail "build --prepare failed with a root directory link: $(cat "$TMP_DIR/refresh-link.log")"
[ -f "$TMP_DIR/victim-root/keep.txt" ] ||
  fail "refresh followed the root directory link and deleted $TMP_DIR/victim-root/keep.txt"
[ -z "$(ls "$TMP_DIR/victim-root"/changes-*.delta.paperlean 2>/dev/null || true)" ] ||
  fail "refresh wrote a pack of changes through the root directory link"
echo "lake-1: ok"
