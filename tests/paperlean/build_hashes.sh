# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests the record of the `.hash` files that builds under `paperlean` commands read
# (`PAPERLEAN_ACCELERATE`, `src/lake/Lake/PaperLean/HashCache.lean`, `.lake/paperlean-hashes.paperlean`),
# which plain `lake` does not use: a build records the files last changed well before it started, and
# a later build takes their hashes from the record while they keep their identity, but reads a file
# that changed since, also one whose modification time was set back, and computes the hash of a file
# that is gone, as Lake does, rebuilding the same modules as plain `lake`; the record holds the files
# that the last build read, and the kept record those that it held besides; a damaged record, or one of
# another build, is ignored; the temporary files of writers that ended are removed; no `.lake/paperlean`
# is made for the record.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN PAPERLEAN_DATA PAPERLEAN_BUILD_PACKS PAPERLEAN_HASH_CACHE PAPERLEAN_ACCELERATE
WS="$(cd "$TMP_DIR" && pwd -P)/ws"
mkdir -p "$WS/Root"
cd "$WS"
cat > lakefile.toml <<'END'
name = "root"
defaultTargets = ["Root"]
[[lean_lib]]
name = "Root"
END
printf 'def a : Nat := 1\n' > Root/A.lean
printf 'import Root.A\ndef b : Nat := a + 1\n' > Root/B.lean
printf 'import Root.B\ndef c : Nat := b + 1\n' > Root/C.lean
printf 'import Root.C\n' > Root.lean
REC=.lake/paperlean-hashes.paperlean
KEPT=.lake/paperlean-hashes-kept.paperlean
LIB=.lake/build/lib/lean/Root
built() { grep -o 'Built Root[.A-Za-z0-9]*' "$CAPTURED.out.produced" | sed 's/Built //' | sort | tr '\n' ' '; }
# flips the lowest bit of byte $2 of file $1
flip() { perl -e 'open F, "+<", $ARGV[0] or die; seek F, $ARGV[1], 0; read F, $c, 1; seek F, $ARGV[1], 0; print F chr(ord($c) ^ 1); close F' "$1" "$2"; }
# the offset in the record of the hash of the file whose path ends in $1
hashAt() { echo $(( $(grep -abo "$1" "$REC" | head -1 | cut -d: -f1) + ${#1} + 56 )); }

run lake build
[ ! -e "$REC" ] || fail "plain lake recorded .hash files"
# files written just before a build are not recorded (written again here, as the plain build may have
# taken longer than the margin; a build that started after the margin, by the time of the file that
# it writes then, is tried again)
for try in 1 2 3; do
  cat $LIB/A.olean.hash > "$TMP_DIR/hash" && cat "$TMP_DIR/hash" > $LIB/A.olean.hash
  run env PAPERLEAN_ACCELERATE=1 lake build
  perl -e 'exit((stat $ARGV[0])[9] - (stat $ARGV[1])[10] > 2)' .lake/paperlean-clock.paperlean \
    $LIB/A.olean.hash && break
done
! grep -aq "Root/A.olean.hash" "$REC" 2> /dev/null || fail "a file written just before the build was recorded"
sleep 3
run env PAPERLEAN_ACCELERATE=1 lake build
grep -aq "Root/A.olean.hash" "$REC" || fail "Root/A.olean.hash was not recorded"
grep -aq "Root/C.ilean.hash" "$REC" || fail "Root/C.ilean.hash was not recorded"
[ ! -e .lake/paperlean ] || fail "the record made .lake/paperlean, without prepared data"
cp "$REC" "$TMP_DIR/record"
# unchanged files: nothing changes, nor does the record
capture env PAPERLEAN_ACCELERATE=1 lake build
[ -z "$(built)" ] || fail "an unchanged build rebuilt $(built)"
cmp -s "$REC" "$TMP_DIR/record" || fail "the record changed without changes"

# A `.hash` file that changed since it was recorded, with its modification time set back as it was,
# is read: Lake then takes the module's `.olean` to have changed and rebuilds the modules that import
# it, as plain `lake` does with the same change in a copy.
cp -R "$WS" "$TMP_DIR/plain"
for d in "$WS" "$TMP_DIR/plain"; do
  cp -p "$d/$LIB/A.olean.hash" "$TMP_DIR/time-ref"
  printf '0123456789abcdef' > "$d/$LIB/A.olean.hash"
  touch -r "$TMP_DIR/time-ref" "$d/$LIB/A.olean.hash"
done
capture env PAPERLEAN_ACCELERATE=1 lake build
case "$(built)" in *Root.B*) ;; *) fail "the changed .hash file was not read: rebuilt $(built)" ;; esac
accelerated=$(built)
(cd "$TMP_DIR/plain" && capture lake build)
[ "$(built)" = "$accelerated" ] || fail "plain lake rebuilt $(built), the accelerated build $accelerated"
dephash() { grep -o '"depHash": *"[0-9a-f]*"' "$1/$LIB/B.trace"; }
[ -n "$(dephash "$WS")" ] && [ "$(dephash "$WS")" = "$(dephash "$TMP_DIR/plain")" ] ||
  fail "the traces of Root.B differ from plain lake's"

# A `.hash` file that is gone is computed again from its file, as plain `lake` does.
rm $LIB/C.ilean.hash
capture env PAPERLEAN_ACCELERATE=1 lake build
[ -z "$(built)" ] || fail "a missing .hash file rebuilt $(built)"
[ -f $LIB/C.ilean.hash ] || fail "the missing .hash file was not written again"
rm "$TMP_DIR/plain/$LIB/C.ilean.hash"
(cd "$TMP_DIR/plain" && run lake build)
cmp $LIB/C.ilean.hash "$TMP_DIR/plain/$LIB/C.ilean.hash" ||
  fail "the .hash file written again differs from plain lake's"

# A record whose entries are damaged is ignored (here the hash of Root/A.olean: were it used, Root.B
# would be rebuilt), and one of another build too; both are written again.
sleep 3
run env PAPERLEAN_ACCELERATE=1 lake build
grep -aq "Root/A.olean.hash" "$REC" || fail "Root/A.olean.hash was not recorded again"
flip "$REC" "$(hashAt Root/A.olean.hash)"
capture env PAPERLEAN_ACCELERATE=1 lake build
[ -z "$(built)" ] || fail "a damaged record was used: rebuilt $(built)"
cp "$REC" "$TMP_DIR/record"
flip "$REC" 40
capture env PAPERLEAN_ACCELERATE=1 lake build
[ -z "$(built)" ] || fail "the record of another build rebuilt $(built)"
cmp -s -n 152 "$REC" "$TMP_DIR/record" || fail "the record of another build was kept"
echo garbage > "$REC"
capture env PAPERLEAN_ACCELERATE=1 lake build
[ -z "$(built)" ] || fail "a damaged record rebuilt $(built)"
cmp -s -n 152 "$REC" "$TMP_DIR/record" && grep -aq "Root/A.olean.hash" "$REC" ||
  fail "the damaged record was not written again"

# A build of part of the workspace keeps the record of what it read, and moves what the record had
# besides to the kept record, which a later build takes it back from; temporary files of writers that
# ended are removed. A damaged kept record is ignored.
touch "$REC.tmp.99999999"
capture env PAPERLEAN_ACCELERATE=1 lake build Root.A
grep -aq "Root/A.olean.hash" "$REC" || fail "Root/A.olean.hash is not in the record"
! grep -aq "Root/C.ilean.hash" "$REC" || fail "the record kept files that the build did not read"
[ ! -e "$REC.tmp.99999999" ] || fail "the temporary file of a writer that ended was kept"
grep -aq "Root/C.ilean.hash" "$KEPT" || fail "Root/C.ilean.hash is not in the kept record"
! grep -aq "Root/A.olean.hash" "$KEPT" || fail "the kept record has what the build read"
capture env PAPERLEAN_ACCELERATE=1 lake build
[ -z "$(built)" ] || fail "a build with the kept record rebuilt $(built)"
grep -aq "Root/C.ilean.hash" "$REC" || fail "Root/C.ilean.hash was not taken back into the record"
! grep -aq "Root/C.ilean.hash" "$KEPT" || fail "the kept record still has what the build took back"
run env PAPERLEAN_ACCELERATE=1 lake build Root.A
echo garbage > "$KEPT"
capture env PAPERLEAN_ACCELERATE=1 lake build
[ -z "$(built)" ] || fail "a damaged kept record rebuilt $(built)"
grep -aq "Root/C.ilean.hash" "$REC" || fail "Root/C.ilean.hash was not recorded again"

# `PAPERLEAN_HASH_CACHE=0` neither reads nor writes the record.
echo garbage > "$REC"
run env PAPERLEAN_ACCELERATE=1 PAPERLEAN_HASH_CACHE=0 lake build
[ "$(cat "$REC")" = garbage ] || fail "PAPERLEAN_HASH_CACHE=0 wrote the record"
