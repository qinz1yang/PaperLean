# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests olean packs (`Lean.PaperLean.OLeanPack`, `LEAN_OLEAN_PACK`): files served from a pack give
# the same results as reading them, files that changed since packing are read from disk instead (also
# when the fast import served them before checking them), an unusable pack (not a pack, changed since
# it was written, also with its modification time restored, of another version) is ignored with a
# warning, and so are the damaged entries of a pack's index, which Lean finds by checksums when it uses
# them, without changing results. Packs are read-only.

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
  let n ← Lean.PaperLean.OLeanPack.create #[args[1]!] args[0]! (sync := args[2]? != some "nosync")
  IO.println s!"packed: {decide (n > 0)}"
EOF
capture lean --run "$TMP_DIR/pack.lean" "$TMP_DIR/init.paperlean" "$ROOT"
check_out_contains "packed: true"
[ "$(stat -c %a "$TMP_DIR/init.paperlean" 2>/dev/null || stat -f %Lp "$TMP_DIR/init.paperlean")" = 444 ] ||
  fail "the pack is not read-only"
# `identity <pack>...`: Lean takes each file as the pack that it holds, as the tests below need to reach
# what lies behind the check of the pack's identity: this writes what the pack's writer records next to
# it (`pack_identity` in `src/paperlean/olean_pack.cpp`), from the file of a pack that its writer wrote
cat > "$TMP_DIR/identity.lean" <<'EOF'
import Lean.PaperLean.OLeanPack
import Lean.PaperLean.System
open Lean.PaperLean
/-- `side_file_checksum` of bytes in words. -/
def checksum (b : ByteArray) : UInt64 := Id.run do
  let k : UInt64 := 0x9e3779b97f4a7c15
  let mut h : UInt64 := 0x50415045524c45
  for i in [0:b.size / 8] do
    let w := (List.range 8).foldl (init := (0 : UInt64)) fun w j =>
      w ||| (b[8 * i + j]!.toUInt64 <<< (8 * j).toUInt64)
    h := (h ^^^ w) * k
    h := h ^^^ (h >>> 29)
  h := h * k
  return h ^^^ (h >>> 32)
def main (args : List String) : IO Unit := do
  let written ← IO.FS.readBinFile (OLeanPack.identityFile args[0]!)
  for a in args.tail do
    let hdr ← (← IO.FS.Handle.mk a .read).read 152
    let some id ← fileIdentity a | throw (IO.userError s!"cannot read {a}")
    -- the header up to its checksum, which is computed with the field zero, then the pack's checksum
    let head := written.extract 0 144
    let tail := hdr.extract 144 152 ++ id
    let sum := checksum (head ++ ByteArray.mk (Array.replicate 8 0) ++ tail)
    let sumBytes := ByteArray.mk ((List.range 8).toArray.map fun j => (sum >>> (8 * j).toUInt64).toUInt8)
    let out := OLeanPack.identityFile a
    if ← System.FilePath.pathExists out then IO.FS.removeFile out
    IO.FS.writeBinFile out (head ++ sumBytes ++ tail)
EOF
identity() { run lean --run "$TMP_DIR/identity.lean" "$TMP_DIR/init.paperlean" "$@"; }

# A pack stays locked until its identity is recorded: a build that finds it under its name meanwhile
# takes a shared lock and finds it usable (`toolchainPack` in `Lake/PaperLean/BuildData.lean`), where it
# would remove it otherwise.
cat > "$TMP_DIR/watch.lean" <<'EOF'
import Lean.PaperLean.OLeanPack
open Lean.PaperLean
def main (args : List String) : IO Unit := do
  let pack : System.FilePath := args[0]!
  repeat
    if ← pack.pathExists then
      let h ← IO.FS.Handle.mk pack .read
      h.lock (exclusive := false)
      let (stale, _) ← OLeanPack.staleness pack.toString
      IO.println s!"usable, {stale} stale"
      return
EOF
for i in 1 2 3 4 5 6; do
  rm -f "$TMP_DIR/race.paperlean" "$TMP_DIR/id-race.paperlean"
  lean --run "$TMP_DIR/watch.lean" "$TMP_DIR/race.paperlean" > "$TMP_DIR/watch.out" 2>&1 &
  WATCH=$!
  capture lean --run "$TMP_DIR/pack.lean" "$TMP_DIR/race.paperlean" "$ROOT"
  wait $WATCH || fail "a pack was found before its identity was recorded: $(cat "$TMP_DIR/watch.out")"
done
rm -f "$TMP_DIR/race.paperlean" "$TMP_DIR/id-race.paperlean"

# The writer keeps little of the pack in memory (`prepare` writes one of gigabytes while compilers
# run): its peak resident memory (Linux's `VmHWM`) grows by much less than the pack's size.
if [ -r /proc/self/status ]; then
  cat > "$TMP_DIR/pack_memory.lean" <<'EOF'
import Lean.PaperLean.OLeanPack
def peakKB : IO Nat := do
  for l in ← IO.FS.lines "/proc/self/status" do
    if l.startsWith "VmHWM:" then
      if let some n := (l.splitOn " ").findSome? String.toNat? then return n
  throw <| IO.userError "no VmHWM"
def main (args : List String) : IO Unit := do
  let before ← peakKB
  let _ ← Lean.PaperLean.OLeanPack.create #[args[1]!] args[0]!
  IO.println s!"grew by {(← peakKB) - before} kB"
EOF
  capture lean --run "$TMP_DIR/pack_memory.lean" "$TMP_DIR/memory.paperlean" "$ROOT"
  GREW=$(sed -n 's/^grew by \([0-9]*\) kB$/\1/p' "$CAPTURED.out.produced")
  SIZE=$(wc -c < "$TMP_DIR/memory.paperlean")
  [ -n "$GREW" ] && [ $((GREW * 1024 * 4)) -lt "$SIZE" ] ||
    fail "writing a pack of $SIZE bytes raised the writer's peak memory by ${GREW:-?} kB"
  rm -f "$TMP_DIR/memory.paperlean"
fi

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
capture env LEAN_PATH="$ROOT" LEAN_OLEAN_PACK="$TMP_DIR/init.paperlean" PAPERLEAN_IMPORT_TIMING=1 lean "$TMP_DIR/test.lean"
check_out_contains "paperlean-timing modules.fast"
# a pack that is not synced to disk before it is renamed (as build packs) serves the same
capture lean --run "$TMP_DIR/pack.lean" "$TMP_DIR/nosync.paperlean" "$ROOT" nosync
check_out_contains "packed: true"
capture env LEAN_PATH="$ROOT" LEAN_OLEAN_PACK="$TMP_DIR/nosync.paperlean" lean "$TMP_DIR/test.lean"
check_out_contains "served from pack: true, read from disk: 0"
grep -v "served from pack" "$CAPTURED.out.produced" | $DIFF -- "$TMP_DIR/expected.out" - ||
  fail "output differs when using the pack written without syncing"

# Replacing a file (same contents, new inode) invalidates its parts of the pack. The fast import
# serves packed files before checking them, and imports again as `importModulesCore` when a check
# fails.
cp "$ROOT/Init/Core.olean" "$TMP_DIR/Core.olean"
rm "$ROOT/Init/Core.olean"
mv "$TMP_DIR/Core.olean" "$ROOT/Init/Core.olean"
capture env LEAN_PATH="$ROOT" LEAN_OLEAN_PACK="$TMP_DIR/init.paperlean" lean "$TMP_DIR/test.lean"
check_out_contains "served from pack: true, read from disk: 3"
grep -v "served from pack" "$CAPTURED.out.produced" | $DIFF -- "$TMP_DIR/expected.out" - ||
  fail "output differs after invalidating part of the pack"
capture env LEAN_PATH="$ROOT" LEAN_OLEAN_PACK="$TMP_DIR/init.paperlean" PAPERLEAN_IMPORT_TIMING=1 lean "$TMP_DIR/test.lean"
check_out_contains "paperlean-timing modules.fallback"
# the files of an abandoned fast import are not counted: the counts are those of `importModulesCore`
cat > "$TMP_DIR/stats.lean" <<'EOF'
import Lean.PaperLean.OLeanPack
#eval show IO Unit from do
  let (served, notServed) ← Lean.PaperLean.OLeanPack.stats
  IO.println s!"served {served}, read from disk {notServed}"
EOF
capture env LEAN_PATH="$ROOT" LEAN_OLEAN_PACK="$TMP_DIR/init.paperlean" PAPERLEAN_IMPORT=legacy lean "$TMP_DIR/stats.lean"
cp "$CAPTURED.out.produced" "$TMP_DIR/stats.legacy.out"
for i in 1 2; do
  capture env LEAN_PATH="$ROOT" LEAN_OLEAN_PACK="$TMP_DIR/init.paperlean" lean "$TMP_DIR/stats.lean"
  $DIFF -- "$TMP_DIR/stats.legacy.out" "$CAPTURED.out.produced" || fail "the counts include an abandoned fast import"
done

# A file that changes while it is packed: its module is left out (the pack would record it as first
# opened), and an import of its importer, which is packed, reads it from disk, with the same result.
# The files come after those of `$ROOT` in the pack, long after they were first looked at.
CHAIN="$TMP_DIR/zchain"
mkdir -p "$CHAIN"
cat > "$TMP_DIR/ChainA.lean" <<'EOF'
def chainA := 1
EOF
cat > "$TMP_DIR/ChainB.lean" <<'EOF'
import ChainA
def chainB := chainA + 1
EOF
cat > "$TMP_DIR/UseChain.lean" <<'EOF'
import ChainB
import Lean.PaperLean.OLeanPack
#eval chainB
#eval show IO Unit from do
  let (served, notServed) ← Lean.PaperLean.OLeanPack.stats
  IO.println s!"served from pack: {decide (served > 0)}, read from disk: {notServed}"
EOF
for m in ChainA ChainB; do
  (cd "$TMP_DIR" && run env LEAN_PATH="$ROOT:$CHAIN" lean -o "$CHAIN/$m.olean" -i "$CHAIN/$m.ilean" "$m.lean")
done
cat > "$TMP_DIR/packChain.lean" <<'EOF'
import Lean.PaperLean.OLeanPack
open Lean.PaperLean
def main (args : List String) : IO Unit := do
  let _ ← OLeanPack.create #[args[1]!, args[2]!] args[0]!
  let (stale, _) ← OLeanPack.staleness args[0]!
  IO.println s!"{stale} stale"
EOF
(while [ ! -e "$TMP_DIR/chain-stop" ]; do touch "$CHAIN/ChainA.olean"; done) &
TOUCHER=$!
capture lean --run "$TMP_DIR/packChain.lean" "$TMP_DIR/chain.paperlean" "$ROOT" "$CHAIN"
touch "$TMP_DIR/chain-stop"
wait $TOUCHER
check_out_contains "0 stale"
capture env LEAN_PATH="$ROOT:$CHAIN" lean "$TMP_DIR/UseChain.lean"
check_out_contains "2"
check_out_contains "served from pack: false, read from disk: 0"
capture env LEAN_PATH="$ROOT:$CHAIN" LEAN_OLEAN_PACK="$TMP_DIR/chain.paperlean" lean "$TMP_DIR/UseChain.lean"
check_out_contains "2"
check_out_contains "served from pack: true, read from disk: 1"
! grep -q "warning" "$CAPTURED.out.produced" || fail "a warning about a module left out: $(cat "$CAPTURED.out.produced")"

# An unusable pack is ignored.
echo "not a pack" > "$TMP_DIR/bad.paperlean"
capture env LEAN_PATH="$ROOT" LEAN_OLEAN_PACK="$TMP_DIR/bad.paperlean" lean "$TMP_DIR/test.lean"
check_out_contains "ignoring olean pack"
check_out_contains "served from pack: false, read from disk: 0"
grep -v -e "served from pack" -e "ignoring olean pack" "$CAPTURED.out.produced" |
  $DIFF -- "$TMP_DIR/expected.out" - || fail "output differs with an unusable pack"

# A pack whose index was written to since it was written is ignored: the index ends the file.
cp "$TMP_DIR/init.paperlean" "$TMP_DIR/damaged.paperlean"
chmod u+w "$TMP_DIR/damaged.paperlean"
identity "$TMP_DIR/damaged.paperlean"
printf 'X' | dd of="$TMP_DIR/damaged.paperlean" bs=1 seek=$(($(wc -c < "$TMP_DIR/damaged.paperlean") - 1)) conv=notrunc 2>/dev/null
capture env LEAN_PATH="$ROOT" LEAN_OLEAN_PACK="$TMP_DIR/damaged.paperlean" lean "$TMP_DIR/test.lean"
check_out_contains "it changed since it was written"
check_out_contains "served from pack: false, read from disk: 0"
grep -v -e "served from pack" -e "ignoring olean pack" "$CAPTURED.out.produced" |
  $DIFF -- "$TMP_DIR/expected.out" - || fail "output differs with a damaged pack"

# Lean checks the header of a pack that has the identity recorded next to it, and, when it first uses
# an entry of the index, the checksums of the blocks it lies in and its bounds: a damaged entry
# (here, damaged with that identity recorded) is not used, with a warning, and results do not change.
# The tables are located by the header's fields (`pack_header` in `src/paperlean/olean_pack.cpp`).
# The pack is written again, as `Init/Core.olean` changed.
capture lean --run "$TMP_DIR/pack.lean" "$TMP_DIR/fresh.paperlean" "$ROOT"
check_out_contains "packed: true"
field() { od -An -t u8 -j "$2" -N 8 "$1" | tr -d ' '; }
# `damaged <name>`: the copy `<name>.paperlean` of the pack, with its identity recorded, gives Lean's
# output, with a warning (the whole pack is ignored if its roots are damaged)
damaged() {
  identity "$TMP_DIR/$1.paperlean"
  capture env LEAN_PATH="$ROOT" LEAN_OLEAN_PACK="$TMP_DIR/$1.paperlean" lean "$TMP_DIR/test.lean"
  check_out_matches "ignoring damaged entries of its index|ignoring olean pack .*: corrupt"
  grep -v -e "served from pack" -e "ignoring damaged entries" -e "ignoring olean pack" "$CAPTURED.out.produced" |
    $DIFF -- "$TMP_DIR/expected.out" - || fail "output differs with a damaged $1"
}
# `damage <name> <offset> <bytes>`: with `<bytes>` bytes at `<offset>` set to 0xff
damage() {
  cp "$TMP_DIR/fresh.paperlean" "$TMP_DIR/$1.paperlean"
  chmod u+w "$TMP_DIR/$1.paperlean"
  perl -e 'open(F, "+<", $ARGV[0]) or die; binmode F; seek(F, $ARGV[1], 0); print F "\xff" x $ARGV[2]; close F' \
    "$TMP_DIR/$1.paperlean" "$2" "$3"
  damaged "$1"
}
# `edit <name> <perl>`: changed by the Perl code `<perl>`, which reads the file with `rd(offset,
# bytes)`, writes it with `wr(offset, bytes)`, and finds the header's fields in `$h`
edit() {
  cp "$TMP_DIR/fresh.paperlean" "$TMP_DIR/$1.paperlean"
  chmod u+w "$TMP_DIR/$1.paperlean"
  perl -e 'open(F, "+<", $ARGV[0]) or die; binmode F;
    sub rd { my ($o, $n) = @_; seek(F, $o, 0); read(F, my $x, $n) == $n or die; $x }
    sub wr { my ($o, $x) = @_; seek(F, $o, 0); print F $x }
    sub u64 { unpack("Q<", substr($_[0], $_[1], 8)) } sub u32 { unpack("L<", substr($_[0], $_[1], 4)) }
    our $h = rd(0, 4096); eval $ARGV[1]; die $@ if $@; close F' "$TMP_DIR/$1.paperlean" "$2"
  damaged "$1"
}
FRESH="$TMP_DIR/fresh.paperlean"
ENTRIES=$(field "$FRESH" 176); MODULES=$(field "$FRESH" 240); NUM_MODULES=$(field "$FRESH" 248)
ROOTS_HASH=$(field "$FRESH" 312); ROOTS_HASH_SIZE=$(field "$FRESH" 320)
PATHS=$(field "$FRESH" 352); PATHS_SIZE=$(field "$FRESH" 360)
# the first entries, of the first chains (`Init.ir.sig` and `Init.ir`, ...), are read from disk
damage entry "$ENTRIES" 8
check_out_matches "served from pack: true, read from disk: [1-9]"
# modules (`pack_module`) are found through the search path
damage modules "$MODULES" $((NUM_MODULES * 48))
check_out_contains "served from pack: true, read from disk: 0"
# no path is found in the pack
damage paths "$PATHS" $((PATHS_SIZE * 8))
check_out_contains "served from pack: false"
# the metadata of packed module data is read from the data (the table shares a block with the roots)
damage roots "$ROOTS_HASH" $((ROOTS_HASH_SIZE * 16))
check_out_contains "read from disk: 0"
# Damage within the bounds of the index. The first `.olean` part with a nonempty entries array of an
# extension gets it under the name of another extension (`pack_ext_entry`) ...
edit ext_name '
  my ($entries, $n, $strings, $parts, $exts, $base) = (u64($h, 176), u64($h, 184), u64($h, 224), u64($h, 272), u64($h, 280), u64($h, 160));
  ENTRY: for my $i (0 .. $n - 1) {
    my $e = rd($entries + 136 * $i, 136);
    next unless rd($strings + u64($e, 80), u64($e, 88)) =~ /\.olean$/;
    my $p = rd($parts + 72 * $i, 72);
    my ($num, $first) = (u32($p, 44), u32($p, 48));
    for my $k (0 .. $num - 1) {
      my $x = rd($exts + 16 * ($first + $k), 16);
      next if u64(rd(u64($x, 0) - $base + 8, 8), 0) == 0;
      for my $j (0 .. $num - 1) {
        my $name = u32(rd($exts + 16 * ($first + $j) + 8, 4), 0);
        next if $name == u32($x, 8);
        wr($exts + 16 * ($first + $k) + 8, pack("L<", $name));
        last ENTRY;
      }
    }
  }'
check_out_contains "served from pack: true, read from disk: 0"
# ... and the first `module` loses its flag (`pack_module_is_module`), with which its parts are read
edit is_module '
  my ($modules, $n) = (u64($h, 240), u64($h, 248));
  for my $i (0 .. $n - 1) {
    my $flags = u32(rd($modules + 48 * $i + 44, 4), 0);
    next unless $flags & 1;
    wr($modules + 48 * $i + 44, pack("L<", $flags & ~1));
    last;
  }'
check_out_contains "served from pack: true, read from disk: 0"

# A pack whose regions were written to since it was written is ignored, even though its index is
# intact: the identity recorded next to it holds the file's modification time, which the write changed.
# Here the copies
# of the modules' root objects, which every import reads, are overwritten (the pack's
# `roots_area_off` and `names_off`, `pack_header` in `src/paperlean/olean_pack.cpp`).
cp -p "$TMP_DIR/init.paperlean" "$TMP_DIR/regions.paperlean"
chmod u+w "$TMP_DIR/regions.paperlean"
identity "$TMP_DIR/regions.paperlean"
ROOTS_AREA=$(field "$TMP_DIR/init.paperlean" 328); NAMES=$(field "$TMP_DIR/init.paperlean" 336)
[ "$NAMES" -gt "$ROOTS_AREA" ] || fail "no roots area at $ROOTS_AREA..$NAMES"
head -c $((NAMES - ROOTS_AREA)) /dev/zero | tr '\0' '\377' |
  dd of="$TMP_DIR/regions.paperlean" bs=1 seek=$ROOTS_AREA conv=notrunc 2>/dev/null
capture env LEAN_PATH="$ROOT" LEAN_OLEAN_PACK="$TMP_DIR/regions.paperlean" lean "$TMP_DIR/test.lean"
check_out_contains "it changed since it was written"
check_out_contains "served from pack: false, read from disk: 0"
grep -v -e "served from pack" -e "ignoring olean pack" "$CAPTURED.out.produced" |
  $DIFF -- "$TMP_DIR/expected.out" - || fail "output differs with a pack whose regions changed"
# Restoring that time does not help: the identity recorded next to the pack holds the file's change
# time, which a write changes and no tool can restore, and the result is that without the pack.
touch -r "$TMP_DIR/init.paperlean" "$TMP_DIR/regions.paperlean"
capture env LEAN_PATH="$ROOT" LEAN_OLEAN_PACK="$TMP_DIR/regions.paperlean" lean "$TMP_DIR/test.lean"
check_out_contains "it changed since it was written"
check_out_contains "served from pack: false, read from disk: 0"
grep -v -e "served from pack" -e "ignoring olean pack" "$CAPTURED.out.produced" |
  $DIFF -- "$TMP_DIR/expected.out" - || fail "output differs with a pack changed with its modification time restored"
# A copy of a pack has another identity.
cp -p "$TMP_DIR/init.paperlean" "$TMP_DIR/copy.paperlean"
capture env LEAN_PATH="$ROOT" LEAN_OLEAN_PACK="$TMP_DIR/copy.paperlean" lean "$TMP_DIR/test.lean"
check_out_contains "it changed since it was written"
check_out_contains "served from pack: false, read from disk: 0"
# `verify` reads the regions: it finds the change even when the file has the recorded identity, which
# Lean does not, as for damage to `.olean` files that leaves their metadata alone.
identity "$TMP_DIR/regions.paperlean"
cat > "$TMP_DIR/verify.lean" <<'EOF'
import Lean.PaperLean.OLeanPack
def main (args : List String) : IO Unit := do
  for a in args do IO.println s!"{a}: [{← Lean.PaperLean.OLeanPack.verify a}]"
EOF
capture lean --run "$TMP_DIR/verify.lean" "$TMP_DIR/init.paperlean" "$TMP_DIR/regions.paperlean" "$TMP_DIR/entry.paperlean"
check_out_contains "$TMP_DIR/init.paperlean: []"
check_out_contains "$TMP_DIR/regions.paperlean: [corrupt (its regions' checksum differs)]"
check_out_contains "$TMP_DIR/entry.paperlean: [corrupt (checksum mismatch)]"

# A side file that is not a regular file does not block `lean`.
mkfifo "$TMP_DIR/fifo"
for v in LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS; do
  capture env LEAN_PATH="$ROOT" $v="$TMP_DIR/fifo" timeout 60 lean "$TMP_DIR/test.lean"
  grep -v -e "served from pack" -e "warning: ignoring" "$CAPTURED.out.produced" |
    $DIFF -- "$TMP_DIR/expected.out" - || fail "output differs with $v set to a FIFO"
done

# A pack written by another version is ignored: the version follows the magic and the kind.
cp "$TMP_DIR/init.paperlean" "$TMP_DIR/other.paperlean"
chmod u+w "$TMP_DIR/other.paperlean"
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
