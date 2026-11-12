# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Regression test for `import-1`: an import image whose name/origin index has a damaged block must
# be declined (with a warning) and the imported state computed by Lean's fold, not used with the
# damaged zero slots taken for empty ones.
#
# Fails on the current toolchain: the image is accepted, and with PAPERLEAN_IMPORT=check the
# replay's imported state of the default simp set differs from the fold ("... differs from the
# fold: ... ctor tag 1 vs 0"), because an unpacked entry for a name the image has gets a dynamic
# class and `lemmaNames` ends up with two equal keys. With the fix the damaged slot is checked (and
# found damaged), the image is declined, the fold runs, and the observable state is the legacy one.
#
# Needs: PaperLean `lean` (LEAN / `lean` on PATH), Python 3, and ~2-4 minutes (1024 small
# theorems + four imports per damaged table). Uses `TMP_DIR` (or mktemp) for its work directory.

set -u
set +e
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
LEAN=${LEAN:-}
if [ -z "${LEAN:-}" ]; then
  LEAN=$(command -v lean) || { echo "no lean; set LEAN" >&2; exit 1; }
fi
[ -x "$LEAN" ] || { echo "LEAN=$LEAN is not executable" >&2; exit 1; }
TC=${TC:-$("$LEAN" --print-libdir)}
N=1024
if [ -n "${TMP_DIR:-}" ]; then
  W="$TMP_DIR/import-image-index"; rm -rf "$W"; mkdir -p "$W"
else
  W=$(mktemp -d "${TMPDIR:-/tmp}/import-image-index.XXXXXX") || exit 1
fi
mkdir -p "$W/src" "$W/lib" "$W/out"
cd "$W/src" || exit 1
export HOME="$W/home" XDG_CACHE_HOME="$W/xdg" PAPERLEAN_CACHE_DIR="$W/pc"
mkdir -p "$HOME" "$PAPERLEAN_CACHE_DIR"
export LAKE_CACHE_DIR=
unset LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING PAPERLEAN_NATIVE_LIBS PAPERLEAN_REUSE PAPERLEAN_EXACT
export LEAN_PATH="$W/lib:$TC"

fail() { echo "FAIL: $*" >&2; [ -f "$W/out/last" ] && cat "$W/out/last" >&2; exit 1; }

# The packed module: 1024 simp lemmas named ImgT.t0 .. ImgT.t1023, so the image's name and origin
# indexes for the default simp set are large (4096 slots, 16 KiB) and have blocks wholly inside them.
{
  echo "import Lean"
  echo "namespace ImgT"
  for i in $(seq 0 $((N - 1))); do
    echo "theorem t$i (n : Nat) : n + $i = $i + n := Nat.add_comm n _"
    echo "attribute [simp] t$i"
  done
  echo "end ImgT"
} > P.lean
cat > pack.lean <<'EOF'
import Lean.PaperLean.OLeanPack
def main (args : List String) : IO Unit := do
  let n ← Lean.PaperLean.OLeanPack.create #[args[1]!] args[0]!
  IO.println s!"packed: {n}"
EOF
cat > image.lean <<'EOF'
import Lean.PaperLean.ImportState
def main (args : List String) : IO Unit := do
  let n ← Lean.PaperLean.writeImportImage args[0]!
  IO.println s!"image entries: {n}"
EOF
cat > hash.lean <<'EOF'
import Lean
open Lean
#eval show IO Unit from do
  for i in [0:1024] do
    let nm := Name.str (Name.str .anonymous "ImgT") s!"t{i}"
    IO.println s!"{i} {nm.hash}"
EOF
cat > Use.lean <<'EOF'
import U
#eval (default : Nat)
EOF

"$LEAN" -o "$W/lib/P.olean" P.lean > "$W/out/P.out" 2> "$W/out/P.err" ||
  { cat "$W/out/P.err" >&2; fail "cannot build P.lean"; }
"$LEAN" --run pack.lean "$W/pack.paperlean" "$W/lib" > "$W/out/pack.out" 2> "$W/out/pack.err" ||
  { cat "$W/out/pack.err" >&2; fail "cannot pack P"; }
LEAN_OLEAN_PACK="$W/pack.paperlean" "$LEAN" --run image.lean "$W/image.paperlean" \
  > "$W/out/image.out" 2> "$W/out/image.err" ||
  { cat "$W/out/image.err" >&2; fail "cannot write the image"; }
"$LEAN" hash.lean > "$W/hashes" 2> "$W/out/hash.err" ||
  { cat "$W/out/hash.err" >&2; fail "cannot hash the names"; }
[ "$(wc -l < "$W/hashes")" = "$N" ] || fail "expected $N name hashes"
echo "built P, pack ($(cat "$W/out/pack.out")), image ($(cat "$W/out/image.out")), hashes"

# Runs Use.lean (which imports U; U imports P) in $1 with the rest of the arguments as env.
run_use() {
  local name=$1; shift
  ( cd "$W/src" && env "$@" "$LEAN" Use.lean ) > "$W/out/$name.out" 2> "$W/out/$name.err"
  echo $? > "$W/out/$name.code"
  cat "$W/out/$name.out" "$W/out/$name.err" > "$W/out/last"
}

for table in ${TABLES:-names origins}; do
  echo "== $table index =="
  if ! python3 "$HERE/import_image_index.py" "$W/image.paperlean" "$W/hashes" "$table" \
        "$W/bad-$table.image.paperlean" > "$W/out/$table.damage" 2>&1; then
    cat "$W/out/$table.damage" >&2
    fail "cannot construct a damaged $table index (image too small?)"
  fi
  cat "$W/out/$table.damage"
  i=$(sed -n 's/^use //p' "$W/out/$table.damage")
  [ -n "$i" ] || fail "no chosen declaration for $table"

  # U is not in the pack: an unpacked module with a simp entry for a name the image has.
  printf 'import P\nopen ImgT\nattribute [simp] t%s\n' "$i" > U.lean
  "$LEAN" -o "$W/lib/U.olean" U.lean > "$W/out/U.out" 2> "$W/out/U.err" ||
    { cat "$W/out/U.err" >&2; fail "cannot build U.lean"; }

  run_use legacy PAPERLEAN_IMPORT=legacy
  [ "$(cat "$W/out/legacy.code")" = 0 ] || fail "the legacy import failed"
  run_use check PAPERLEAN_IMPORT=check
  [ "$(cat "$W/out/check.code")" = 0 ] || fail "PAPERLEAN_IMPORT=check failed without an image"
  run_use image_ok PAPERLEAN_IMPORT=check LEAN_OLEAN_PACK="$W/pack.paperlean" LEAN_IMPORT_IMAGE="$W/image.paperlean"
  [ "$(cat "$W/out/image_ok.code")" = 0 ] || fail "the undamaged image failed under check (test is invalid)"
  cmp -s "$W/out/legacy.out" "$W/out/image_ok.out" || fail "the undamaged image changed the output"

  bad="$W/bad-$table.image.paperlean"
  run_use image_bad PAPERLEAN_IMPORT=check LEAN_OLEAN_PACK="$W/pack.paperlean" LEAN_IMPORT_IMAGE="$bad"
  code=$(cat "$W/out/image_bad.code")
  if [ "$code" != 0 ]; then
    fail "the damaged $table index was not declined under check (exit $code):
$(grep -m1 'PAPERLEAN_IMPORT=check:' "$W/out/image_bad.out" "$W/out/image_bad.err" 2>/dev/null)"
  fi
  grep -q "differs from the fold" "$W/out/image_bad.out" "$W/out/image_bad.err" &&
    fail "the damaged $table index produced a state that differs from the fold"
  grep -q "warning: ignoring the import image's tables" "$W/out/image_bad.err" ||
    fail "the damaged $table index was not reported as damaged (no warning)"
  cmp -s "$W/out/legacy.out" "$W/out/image_bad.out" ||
    fail "the damaged $table index changed the output under check"

  run_use image_bad_fast PAPERLEAN_IMPORT= LEAN_OLEAN_PACK="$W/pack.paperlean" LEAN_IMPORT_IMAGE="$bad"
  [ "$(cat "$W/out/image_bad_fast.code")" = 0 ] || fail "the damaged $table index failed without check"
  grep -q "warning: ignoring the import image's tables" "$W/out/image_bad_fast.err" ||
    fail "the damaged $table index was not reported as damaged without check (no warning)"
  cmp -s "$W/out/legacy.out" "$W/out/image_bad_fast.out" ||
    fail "the damaged $table index changed the output without check"
  echo "ok: $table index"
done
echo "All import image index damage tests passed."
