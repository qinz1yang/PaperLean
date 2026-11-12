# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that a prepare that keeps dependency data must not
# change env.json's cache root while retaining paths relative to the old one.
if [ -z "${TMP_DIR:-}" ]; then
  TMP_DIR="$(mktemp -d)"
  trap 'rm -rf "$TMP_DIR"' EXIT
fi
# (run_test.sh defines `fail`; a direct run does not)
if ! declare -F fail > /dev/null; then
  fail() { echo "TEST FAILED: $1"; exit 1; }
fi
CACHE_A="$TMP_DIR/cache-a"
CACHE_B="$TMP_DIR/cache-b"
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
PAPERLEAN_CACHE_DIR="$CACHE_A" lake build > "$TMP_DIR/build.log" 2>&1 || fail "the initial build failed"
PAPERLEAN_CACHE_DIR="$CACHE_A" lake paperlean prepare -j 2 > "$TMP_DIR/prepare-a.log" 2>&1 ||
  fail "prepare in cache A failed"
PAPERLEAN_CACHE_DIR="$CACHE_B" lake paperlean prepare root -j 2 > "$TMP_DIR/prepare-root-b.log" 2>&1 ||
  fail "prepare root in cache B failed: $(cat "$TMP_DIR/prepare-root-b.log")"
PAPERLEAN_CACHE_DIR="$CACHE_B" lake paperlean status > "$TMP_DIR/status-b.log" 2>&1 ||
  fail "status failed"
! grep -Eq 'missing|used in part|not used|unavailable' "$TMP_DIR/status-b.log" ||
  fail "prepare root left data in the old cache: $(cat "$TMP_DIR/status-b.log")"
python3 - "$WS/.lake/paperlean/env.json" <<'PY' || exit 1
import json, os, sys
d = json.load(open(sys.argv[1]))
cache = d['cache']
data = os.path.dirname(sys.argv[1])
refs = [os.path.join(data, p) for p in d.get('packs', [])]
if d.get('image'):
    refs.append(os.path.join(data, d['image']))
for p in d.get('deps', []):
    if p.get('binding'):
        refs.append(os.path.join(data, p['binding']))
    if p.get('pack'):
        refs.append(os.path.join(cache, p['pack'], 'pack.paperlean'))
for p in d.get('native', []):
    refs.append(os.path.join(cache, p))
for p in d.get('libs', []):
    for f in (p.get('entry'), p.get('lib'), p.get('manifest')):
        if f:
            refs.append(os.path.join(cache, f))
if d.get('toolchain'):
    refs.append(os.path.join(cache, d['toolchain']))
missing = [p for p in refs if not os.path.exists(p)]
if missing:
    print('missing prepared-data files:')
    for p in missing[:10]: print(' ', p)
    raise SystemExit(1)
print('all prepared-data paths exist under', cache)
PY
echo "lake-2: ok"
