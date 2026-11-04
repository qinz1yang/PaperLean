# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that `paperlean prepare` is incremental: after a module of one dependency package changed, it
# packs that package again and compiles the one unit of its native library that holds the module (the
# objects of the others are in the cache), and takes the data of the other packages from the cache. The
# results are those without prepared data. Workspace: root requires b (which requires a) and c, whose
# library has many modules.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN
ROOT="$(cd "$TMP_DIR" && pwd -P)"
CACHE="$PAPERLEAN_CACHE_DIR/prepared"
mkdir -p "$ROOT/a" "$ROOT/b" "$ROOT/c/C" "$ROOT/ws"
lib() {  # <package dir> <name> <library> [required package]
  {
    echo "name = \"$2\""
    echo "defaultTargets = [\"$3\"]"
    if [ -n "${4:-}" ]; then printf '[[require]]\nname = "%s"\npath = "../%s"\n' "$4" "$4"; fi
    printf '[[lean_lib]]\nname = "%s"\n' "$3"
  } > "$ROOT/$1/lakefile.toml"
}
lib a a A
lib b b B a
lib c c C
echo 'def aValue (n : Nat) : Nat := n + 1' > "$ROOT/a/A.lean"
printf 'import A\ndef bValue (n : Nat) : Nat := aValue n * 2\n' > "$ROOT/b/B.lean"
for i in $(seq 1 100); do echo "def c$i (n : Nat) : Nat := n + $i" > "$ROOT/c/C/M$i.lean"; echo "import C.M$i" >> "$ROOT/c/C.lean"; done
cat > "$ROOT/ws/lakefile.toml" <<'END'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "b"
path = "../b"
[[require]]
name = "c"
path = "../c"
[[lean_lib]]
name = "Root"
END
printf 'import B\nimport C\n#eval bValue 2 + c7 1 + c100 0\n' > "$ROOT/ws/Root.lean"
cd "$ROOT/ws"
run lake build B C

check_use() {
  capture lake lean Root.lean
  cp "$CAPTURED.out.produced" "$TMP_DIR/plain.out"
  capture env PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean Root.lean
  check_out_matches "paperlean-timing native libs=3 "
  { grep -v "^paperlean-" "$CAPTURED.out.produced" || true; } | $DIFF -- "$TMP_DIR/plain.out" - ||
    fail "the prepared data changes the output $1"
}
objects() { ls "$CACHE"/*/objects/*.o | sort; }

capture lake paperlean prepare -j 2
for p in a b c; do check_out_contains "Packing $p"; check_out_contains "Compiling the native library of $p"; done
units=$(sed -n 's/^Compiling the native library of c (.*, \([0-9]*\) units)\.\.\.$/\1/p' "$CAPTURED.out.produced")
[ "${units:-0}" -gt 1 ] || fail "c's library has one unit, which shows nothing: $units"
check_use "after the first prepare"
objects > "$TMP_DIR/objects.before"
env_before=$(cat .lake/paperlean/env.json)

# One module of c changes.
echo 'def c7 (n : Nat) : Nat := n + 70' > "$ROOT/c/C/M7.lean"
(cd "$ROOT/c" && run lake build)
capture lake paperlean prepare -j 2
check_out_contains "Packing c"
check_out_contains "Compiling the native library of c"
for p in a b; do
  ! grep -q "Packing $p\|Compiling the native library of $p" "$CAPTURED.out.produced" || fail "prepare made $p's data again"
done
check_out_contains "Writing the import image"
objects > "$TMP_DIR/objects.after"
new=$(comm -13 "$TMP_DIR/objects.before" "$TMP_DIR/objects.after")
[ "$(echo "$new" | grep -c .)" = 1 ] || fail "not one object compiled again: $new"
check_use "after a module of c changed"
# the entries of a and b are those of before; c's pack and library are new
for p in a b; do
  [ "$(grep -o "\"prepared/[^\"]*/\(pack\|native\)/$p-[0-9a-f]*" .lake/paperlean/env.json | sort -u)" = \
    "$(echo "$env_before" | grep -o "\"prepared/[^\"]*/\(pack\|native\)/$p-[0-9a-f]*" | sort -u)" ] ||
    fail "the entries of $p changed"
done
[ "$(ls -d "$CACHE"/*/pack/c-* | wc -l | tr -d ' ')" = 2 ] || fail "not two packs of c in the cache"
