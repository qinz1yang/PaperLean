# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
cd "$TMP_DIR"
export PAPERLEAN_CACHE_DIR="$PWD/trusted" PAPERLEAN_SOURCE_INPUT_CACHE=1 PAPERLEAN_SOURCE_INPUT_STATS=1
mkdir -p "$PAPERLEAN_CACHE_DIR" workspace
cd workspace
cat > lakefile.lean <<'LEAN'
import Lake
open Lake DSL
package readFacts
lean_lib Protected
lean_lib Good
lean_lib Evil
script readHeader do
  let ws ← getWorkspace
  let some mod := ws.findModule? `Protected | error "missing Protected"
  let input ← ws.runBuild do return (← mod.input.fetch)
  IO.println s!"INPUT-FACTS {input.header.isModule} {input.trace.hash} {input.imports.map (·.module)}"
  return 0
LEAN
printf 'module\n@[expose] public def good := 7\n' > Good.lean
printf 'module\n@[expose] public def evil := 9\n' > Evil.lean
printf 'module\npublic meta import Good\r\n-- α\n' > Protected.lean
sleep 3
run env PAPERLEAN_ACCELERATE=0 lake run readHeader
env PAPERLEAN_ACCELERATE=1 lake run readHeader > "$TMP_DIR/populated.out" 2>&1 || fail "could not populate facts"
grep -q 'INPUT-FACTS .*Good' "$TMP_DIR/populated.out" || fail "wrong initial imports"

env PAPERLEAN_ACCELERATE=1 lake run readHeader > "$TMP_DIR/warm.out" 2>&1 || fail "warm source query failed"
grep -Eq 'PaperLean source inputs: hits=[1-9]' "$TMP_DIR/warm.out" || fail "permission test had no true cache hit"
record="$(find "$PAPERLEAN_CACHE_DIR/prepared" -path '*/inputs/*.paperlean' -type f | head -1)"
[ -f "$record" ] || fail "missing trusted source record"

if [ "$(uname -s)" = Darwin ] && [ -x /usr/bin/sandbox-exec ]; then
  source_path="$(pwd -P)/Protected.lean"
  policy="(version 1)(allow default)(deny file-read-data (literal \"$source_path\"))"
  before=$(/usr/bin/stat -f '%d:%i:%z:%m:%c' "$source_path")
  under=$(/usr/bin/sandbox-exec -p "$policy" /usr/bin/stat -f '%d:%i:%z:%m:%c' "$source_path") ||
    fail "metadata probe failed under sandbox"
  [ "$under" = "$before" ] || fail "sandbox changed the source identity"
  if /usr/bin/sandbox-exec -p "$policy" /bin/cat "$source_path" >/dev/null 2>&1; then
    fail "sandbox did not deny data access"
  fi
  for mode in 0 1; do
    if /usr/bin/sandbox-exec -p "$policy" /usr/bin/env PAPERLEAN_ACCELERATE="$mode" lake run readHeader \
      > "$TMP_DIR/denied-$mode.out" 2>&1; then
      fail "input query returned source facts without read permission"
    fi
    grep -q 'Protected.lean' "$TMP_DIR/denied-$mode.out" || fail "input did not fail on its denied source"
  done
fi

# A complete, correctly checksummed but false record in the workspace is never an input authority.
cat > "$TMP_DIR/ForgeRecord.lean" <<'LEAN'
import Init
open System
def main (args : List String) : IO Unit := do
  let [src, dst] := args | throw (IO.userError "need trusted input and untrusted output")
  let bytes ← IO.FS.readBinFile src
  let some nl := bytes.data.findIdx? (· == 10) | throw (IO.userError "no prefix")
  let preLen := nl + 1
  let workspaceLen := (List.range 4).foldl (init := 0) fun n j =>
    n ||| bytes[preLen+j]!.toNat <<< (8*j)
  let stamp := preLen + 4 + workspaceLen
  let mut body := bytes.extract (stamp+8) bytes.size
  let good := #[4,0,0,0].toList.map UInt8.ofNat |>.toArray |> ByteArray.mk
  let pattern := good ++ "Good".toUTF8
  let replacements := "Evil".toUTF8
  let mut found := 0
  for j in [0:body.size] do
    if body.extract j (j+pattern.size) == pattern then
      for k in [0:4] do body := body.set! (j+4+k) replacements[k]!
      found := found + 1
  unless found == 1 do throw (IO.userError s!"expected one parsed name, found {found}")
  let checksum := body.hash
  let suffix := (List.range 8).foldl (init := ByteArray.empty) fun b i =>
    b.push (checksum >>> (8*i).toUInt64).toUInt8
  IO.FS.writeBinFile dst (bytes.extract 0 stamp ++ suffix ++ body)
LEAN
untrusted=.lake/paperlean-source-inputs.paperlean
run lean --run "$TMP_DIR/ForgeRecord.lean" "$record" "$untrusted"
mv "$record" "$TMP_DIR/private-backup.paperlean"
env PAPERLEAN_ACCELERATE=1 lake run readHeader > "$TMP_DIR/project.out" 2>&1 || fail "untrusted workspace record broke compilation"
grep -q 'PaperLean source inputs: hits=0' "$TMP_DIR/project.out" || fail "project-local record was reused"
grep -q 'INPUT-FACTS .*Good' "$TMP_DIR/project.out" || fail "a rechecksummed workspace record replaced the source's imports"
! grep -q 'INPUT-FACTS .*Evil' "$TMP_DIR/project.out" || fail "forged import was served"

# A same-length edit and restored mtime retain the old inode, but not its ctime.
python3 - Protected.lean <<'PYTHON'
import os, sys
path = sys.argv[1]
before = os.stat(path)
with open(path, "r+b") as f:
    old = f.read()
    assert old.count(b"Good") == 1
    f.seek(0)
    f.write(old.replace(b"Good", b"Evil"))
os.utime(path, ns=(before.st_atime_ns, before.st_mtime_ns))
after = os.stat(path)
assert (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) == (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns)
assert before.st_ctime_ns != after.st_ctime_ns
PYTHON
env PAPERLEAN_ACCELERATE=1 lake run readHeader > "$TMP_DIR/edited.out" 2>&1 || fail "source reread failed"
grep -q 'PaperLean source inputs: hits=0' "$TMP_DIR/edited.out" || fail "cached imports survived source edit"
grep -q 'INPUT-FACTS .*Evil' "$TMP_DIR/edited.out" || fail "same-length edit did not change the parsed inputs"

# Replacing the selected source with a FIFO must consume its one writer through Lake's ordinary path.
rm Protected.lean
mkfifo Protected.lean
( printf 'module\npublic import Evil\n' > Protected.lean ) &
writer=$!
if ! timeout 20 env PAPERLEAN_ACCELERATE=1 lake run readHeader > "$TMP_DIR/fifo.out" 2>&1; then
  kill "$writer" 2>/dev/null || true
  fail "selected FIFO source did not complete with its ordinary single reader"
fi
wait "$writer" || fail "source FIFO writer failed"
grep -q 'INPUT-FACTS .*Evil' "$TMP_DIR/fifo.out" || fail "old regular-file imports were reused for a FIFO"
