# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that the paths of an `env.json` of prepared data (`.lake/paperlean/`,
# `src/lake/Lake/PaperLean/Env.lean`) are checked when it is read: one that `paperlean prepare` does
# not write (with `..`, absolute) makes it unusable, like damaged JSON. A data directory that is a
# symbolic link to another disk works: `prepare` keeps one generation there and `clean` empties it,
# keeping the link; so does a `.lake` that is a link. A file in place of the data directory, or a
# directory in place of `env.json.tmp`, does not stop `prepare`, and `clean` deletes the file.

export XDG_CACHE_HOME="$(cd "$TMP_DIR" && pwd -P)/cache"
WS="$(cd "$TMP_DIR" && pwd -P)/ws"
mkdir -p "$WS"
cd "$WS"
cat > lakefile.toml <<'END'
name = "p"
defaultTargets = ["P"]
[[lean_lib]]
name = "P"
END
echo 'def p : Nat := 1' > P.lean
run lake build
capture lake paperlean prepare p --no-native
check_out_contains "Prepared"
cp .lake/paperlean/env.json "$TMP_DIR/env.json"
ROOT=$(grep -o '"root-[0-9]*/root.paperlean"' .lake/paperlean/env.json)
[ -n "$ROOT" ] || fail "no pack of p in env.json"
# directories with a file that must stay: in the workspace and beside it
VICTIMS="$WS/victim $TMP_DIR/outside"
for v in $VICTIMS; do mkdir -p "$v"; echo keep > "$v/keep.txt"; done
intact() {
  for v in $VICTIMS; do [ -f "$v/keep.txt" ] || fail "$1 deleted $v/keep.txt"; done
}
# `env.json` as prepared, with the packs $1 (the items of a JSON list)
packs() {
  cp "$TMP_DIR/env.json" .lake/paperlean/env.json
  PACKS="$1" perl -0pi -e 's/"packs":\s*\[[^\]]*\]/"packs": [$ENV{PACKS}]/' .lake/paperlean/env.json
  grep -qF "$1" .lake/paperlean/env.json || fail "env.json was not changed"
}

# Paths that leave the data directory, or are absolute: the data is damaged; nothing is deleted.
mkdir -p .lake/paperlean/root-1
for bad in '"root-1/../../../victim/root.paperlean", "root-1/../../../../outside/root.paperlean"' \
    "\"$TMP_DIR/outside/root.paperlean\"" '"root-1/../root-1/root.paperlean"' '"root-1/"' '"root-x/root.paperlean"'; do
  packs "$bad"
  capture lake paperlean status
  check_out_contains "is not a path of prepared data"
  capture env PAPERLEAN_ACCELERATE=1 lake env sh -c 'echo "packs=$LEAN_OLEAN_PACK"'
  ! grep -q paperlean "$CAPTURED.out.produced" || fail "a damaged env.json is used"
  capture lake paperlean build
  check_out_contains "PaperLean prepared data: not used"
  capture lake paperlean clean p
  intact "clean p"
  # (reset without trusting its paths)
  ! grep -q "root-1/\|$TMP_DIR" .lake/paperlean/env.json || fail "clean p kept the paths of a damaged env.json"
  capture lake paperlean status
  check_out_contains "none prepared"
done
echo keep > "$TMP_DIR/outside.delta.paperlean"
for bad in "$ROOT, \"root-1/../../../../outside.delta.paperlean\"" "$ROOT, \"$TMP_DIR/outside.delta.paperlean\""; do
  packs "$bad"
  capture lake paperlean build --prepare
  [ -f "$TMP_DIR/outside.delta.paperlean" ] || fail "build --prepare deleted a file outside the data directory"
done

# A link in place of the data directory, as to a larger disk: each `prepare` deletes the data of the
# one before, also there, `paperlean build` uses it, and `clean` deletes it and keeps the link.
capture lake paperlean clean
LINKED_DATA="$TMP_DIR/linked-data"
mkdir -p "$LINKED_DATA"
rm -rf .lake/paperlean
ln -s "$LINKED_DATA" .lake/paperlean
capture lake paperlean prepare p --no-native
capture lake paperlean prepare p --no-native
capture lake paperlean prepare p --no-native
[ "$(ls -d "$LINKED_DATA"/root-* | wc -l)" -eq 1 ] || fail "prepare kept the data of earlier runs: $(ls "$LINKED_DATA")"
capture lake paperlean build
check_out_contains "PaperLean prepared data: used"
capture lake paperlean clean p
capture lake paperlean clean
[ -L .lake/paperlean ] || fail "clean deleted the link at the data directory"
[ -z "$(ls -A "$LINKED_DATA")" ] || fail "clean left data behind the link: $(ls "$LINKED_DATA")"
rm .lake/paperlean

# A file in place of the data directory, and a directory in place of `env.json`'s temporary file.
echo damage > .lake/paperlean
capture lake paperlean clean
[ ! -e .lake/paperlean ] || fail "clean left a file in place of the data directory"
echo damage > .lake/paperlean
capture lake paperlean prepare p --no-native
check_out_contains "Prepared"
mkdir .lake/paperlean/env.json.tmp
capture lake paperlean prepare p --no-native
check_out_contains "Prepared"

# `.lake` as a link, as when builds are kept on another disk, is the workspace's choice and changes
# nothing: what a command deletes is still deleted.
capture lake paperlean clean
mv .lake "$TMP_DIR/lake-elsewhere"
ln -s "$TMP_DIR/lake-elsewhere" .lake
capture lake paperlean prepare p --no-native
mkdir -p .lake/paperlean/deps-1 .lake/paperlean/build/99999999
capture lake paperlean build
[ ! -e .lake/paperlean/build/99999999 ] || fail "paperlean build kept the packs of a build that ended, with .lake a link"
capture lake paperlean prepare p --no-native
[ ! -e .lake/paperlean/deps-1 ] || fail "prepare kept an unreferenced directory, with .lake a link"
capture lake paperlean clean
[ ! -e .lake/paperlean ] || fail "clean kept the data, with .lake a link"
