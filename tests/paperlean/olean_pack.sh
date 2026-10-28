# Tests olean packs (`Lean.PaperLean.OLeanPack`, `LEAN_OLEAN_PACK`): files served from a pack give
# the same results as reading them, files that changed since packing are read from disk instead, and
# an unusable pack (not a pack, damaged, changed since it was written, of another version) is
# ignored with a warning.

unset LEAN_OLEAN_PACK
LIB="$(lean --print-libdir)"
ROOT="$TMP_DIR/lib"
# A copy of `Init`: hard links would change the ctime of the toolchain's files, which packs that
# other tests make at the same time record.
(cd "$LIB" && find Init Init.* -type f ! -name '*.hash' \( -name '*.olean*' -o -name '*.ir' -o -name '*.ir.sig' \)) |
  while read -r f; do
    mkdir -p "$ROOT/$(dirname "$f")"
    cp "$LIB/$f" "$ROOT/$f"
  done

cat > "$TMP_DIR/pack.lean" <<'EOF'
import Lean.PaperLean.OLeanPack
def main (args : List String) : IO Unit := do
  let n ← Lean.PaperLean.OLeanPack.create #[args[1]!] args[0]!
  IO.println s!"packed: {decide (n > 0)}"
EOF
capture lean --run "$TMP_DIR/pack.lean" "$TMP_DIR/init.paperlean" "$ROOT"
check_out_contains "packed: true"

cat > "$TMP_DIR/test.lean" <<'EOF'
import Lean.PaperLean.OLeanPack
open Lean

#eval show IO Unit from do
  let (served, notServed) ← PaperLean.OLeanPack.stats
  IO.println s!"served from pack: {decide (served > 0)}, read from disk: {notServed}"

theorem t (xs : List Nat) : (xs ++ []).length = xs.length := by simp
#print axioms t
#eval (List.range 100).foldl (· + ·) 0
#check @Nat.add_comm
EOF

capture env LEAN_PATH="$ROOT" lean "$TMP_DIR/test.lean"
check_out_contains "served from pack: false, read from disk: 0"
grep -v "served from pack" "$CAPTURED.out.produced" > "$TMP_DIR/expected.out"

capture env LEAN_PATH="$ROOT" LEAN_OLEAN_PACK="$TMP_DIR/init.paperlean" lean "$TMP_DIR/test.lean"
check_out_contains "served from pack: true, read from disk: 0"
grep -v "served from pack" "$CAPTURED.out.produced" | $DIFF -- "$TMP_DIR/expected.out" - ||
  fail "output differs when using the pack"

# Replacing a file (same contents, new inode) invalidates its parts of the pack.
cp "$ROOT/Init/Core.olean" "$TMP_DIR/Core.olean"
rm "$ROOT/Init/Core.olean"
mv "$TMP_DIR/Core.olean" "$ROOT/Init/Core.olean"
capture env LEAN_PATH="$ROOT" LEAN_OLEAN_PACK="$TMP_DIR/init.paperlean" lean "$TMP_DIR/test.lean"
check_out_contains "served from pack: true, read from disk: 3"
grep -v "served from pack" "$CAPTURED.out.produced" | $DIFF -- "$TMP_DIR/expected.out" - ||
  fail "output differs after invalidating part of the pack"

# An unusable pack is ignored.
echo "not a pack" > "$TMP_DIR/bad.paperlean"
capture env LEAN_PATH="$ROOT" LEAN_OLEAN_PACK="$TMP_DIR/bad.paperlean" lean "$TMP_DIR/test.lean"
check_out_contains "ignoring olean pack"
check_out_contains "served from pack: false, read from disk: 0"
grep -v -e "served from pack" -e "ignoring olean pack" "$CAPTURED.out.produced" |
  $DIFF -- "$TMP_DIR/expected.out" - || fail "output differs with an unusable pack"

# A pack whose index is damaged is ignored: the index ends the file.
cp "$TMP_DIR/init.paperlean" "$TMP_DIR/damaged.paperlean"
printf 'X' | dd of="$TMP_DIR/damaged.paperlean" bs=1 seek=$(($(wc -c < "$TMP_DIR/damaged.paperlean") - 1)) conv=notrunc 2>/dev/null
capture env LEAN_PATH="$ROOT" LEAN_OLEAN_PACK="$TMP_DIR/damaged.paperlean" lean "$TMP_DIR/test.lean"
check_out_contains "checksum mismatch"
check_out_contains "served from pack: false, read from disk: 0"
grep -v -e "served from pack" -e "ignoring olean pack" "$CAPTURED.out.produced" |
  $DIFF -- "$TMP_DIR/expected.out" - || fail "output differs with a damaged pack"

# A pack whose regions were written to since it was written is ignored, even though its index is
# intact: its writer recorded the file's modification time, which the write changed. Here the copies
# of the modules' root objects, which every import reads, are overwritten (the pack's
# `roots_area_off` and `names_off`, `pack_header` in `src/paperlean/olean_pack.cpp`).
cp -p "$TMP_DIR/init.paperlean" "$TMP_DIR/regions.paperlean"
field() { od -An -t u8 -j "$1" -N 8 "$TMP_DIR/init.paperlean" | tr -d ' '; }
ROOTS_AREA=$(field 328); NAMES=$(field 336)
[ "$NAMES" -gt "$ROOTS_AREA" ] || fail "no roots area at $ROOTS_AREA..$NAMES"
head -c $((NAMES - ROOTS_AREA)) /dev/zero | tr '\0' '\377' |
  dd of="$TMP_DIR/regions.paperlean" bs=1 seek=$ROOTS_AREA conv=notrunc 2>/dev/null
capture env LEAN_PATH="$ROOT" LEAN_OLEAN_PACK="$TMP_DIR/regions.paperlean" lean "$TMP_DIR/test.lean"
check_out_contains "it changed since it was written"
check_out_contains "served from pack: false, read from disk: 0"
grep -v -e "served from pack" -e "ignoring olean pack" "$CAPTURED.out.produced" |
  $DIFF -- "$TMP_DIR/expected.out" - || fail "output differs with a pack whose regions changed"
# `verify` reads the regions: it finds the change even with the writer's modification time restored.
touch -r "$TMP_DIR/init.paperlean" "$TMP_DIR/regions.paperlean"
cat > "$TMP_DIR/verify.lean" <<'EOF'
import Lean.PaperLean.OLeanPack
def main (args : List String) : IO Unit := do
  for a in args do IO.println s!"{a}: [{← Lean.PaperLean.OLeanPack.verify a}]"
EOF
capture lean --run "$TMP_DIR/verify.lean" "$TMP_DIR/init.paperlean" "$TMP_DIR/regions.paperlean"
check_out_contains "$TMP_DIR/init.paperlean: []"
check_out_contains "$TMP_DIR/regions.paperlean: [corrupt (its regions' checksum differs)]"

# A pack written by another version is ignored: the version follows the magic and the kind.
cp "$TMP_DIR/init.paperlean" "$TMP_DIR/other.paperlean"
printf '9' | dd of="$TMP_DIR/other.paperlean" bs=1 seek=32 conv=notrunc 2>/dev/null
capture env LEAN_PATH="$ROOT" LEAN_OLEAN_PACK="$TMP_DIR/other.paperlean" lean "$TMP_DIR/test.lean"
check_out_contains "written by a different version"
check_out_contains "served from pack: false, read from disk: 0"

# A file with another Lean's githash gives the same result from the pack as from the disk (an
# error in builds that check it, `CHECK_OLEAN_VERSION`, as Lean's releases do).
ROOT2="$TMP_DIR/lib2"
cp -r "$ROOT" "$ROOT2"
printf 'X' | dd of="$ROOT2/Init/Core.olean" bs=1 seek=40 conv=notrunc 2>/dev/null
capture lean --run "$TMP_DIR/pack.lean" "$TMP_DIR/foreign.paperlean" "$ROOT2"
check_out_contains "packed: true"
capture_only "" env LEAN_PATH="$ROOT2" lean "$TMP_DIR/test.lean"
DISK_EXIT=$EXIT
grep -v "served from pack" "$CAPTURED.out.produced" > "$TMP_DIR/foreign-disk.out"
capture_only "" env LEAN_PATH="$ROOT2" LEAN_OLEAN_PACK="$TMP_DIR/foreign.paperlean" lean "$TMP_DIR/test.lean"
[ "$EXIT" = "$DISK_EXIT" ] || fail "exit code $EXIT from the pack, $DISK_EXIT from the disk"
grep -v "served from pack" "$CAPTURED.out.produced" | $DIFF -- "$TMP_DIR/foreign-disk.out" - ||
  fail "a file with another githash gives another result from the pack"
