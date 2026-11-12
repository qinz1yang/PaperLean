# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# `writeFileIfNew` and `writeBinFileIfNew` publish content-addressed cache
# files.  A concurrent reader must never observe the final path with a size
# between zero and the complete content, and an existing file must still be
# left untouched.

WS="$TMP_DIR/lake-atomic"
mkdir -p "$WS"
cd "$WS"
cat > Publication.lean <<'LEAN'
import Lake.Util.IO

open System Lake

def publishString (dir : FilePath) (i : Nat) : IO Unit := do
  let content := String.ofList (List.replicate (32 * 1024 * 1024) 'x')
  let full := content.utf8ByteSize.toUInt64
  let path := dir / s!"text{i}.txt"
  try IO.FS.removeFile path catch _ => pure ()
  let writer ← IO.asTask (writeFileIfNew path content)
  let mut done := false
  let mut partialCount := 0
  while !done do
    done := ← IO.hasFinished writer
    match (← path.metadata.toBaseIO) with
    | .ok m => if m.byteSize < full then partialCount := partialCount + 1
    | .error _ => pure ()
  if partialCount > 0 then
    IO.eprintln s!"writeFileIfNew exposed a partial final file {partialCount} times"
    IO.Process.exit 1

def publishBytes (dir : FilePath) (i : Nat) : IO Unit := do
  let bytes := String.ofList (List.replicate (32 * 1024 * 1024) 'y') |>.toUTF8
  let full := bytes.size.toUInt64
  let path := dir / s!"bin{i}.bin"
  try IO.FS.removeFile path catch _ => pure ()
  let writer ← IO.asTask (writeBinFileIfNew path bytes)
  let mut done := false
  let mut partialCount := 0
  while !done do
    done := ← IO.hasFinished writer
    match (← path.metadata.toBaseIO) with
    | .ok m => if m.byteSize < full then partialCount := partialCount + 1
    | .error _ => pure ()
  if partialCount > 0 then
    IO.eprintln s!"writeBinFileIfNew exposed a partial final file {partialCount} times"
    IO.Process.exit 1

def main : IO Unit := do
  let dir ← IO.currentDir
  for i in [0, 1, 2] do
    publishString dir i
  for i in [0, 1, 2] do
    publishBytes dir i
  -- An existing file is still not overwritten.
  let keep := dir / "keep.txt"
  writeFileIfNew keep "first\n"
  writeFileIfNew keep "second\n"
  if (← IO.FS.readFile keep) != "first\n" then
    IO.eprintln "writeFileIfNew overwrote an existing file"
    IO.Process.exit 1
  let keepBin := dir / "keep.bin"
  writeBinFileIfNew keepBin "one".toUTF8
  writeBinFileIfNew keepBin "two".toUTF8
  if (← IO.FS.readBinFile keepBin) != "one".toUTF8 then
    IO.eprintln "writeBinFileIfNew overwrote an existing file"
    IO.Process.exit 1
LEAN
run lean --run Publication.lean
# No temporary publication file is left behind.
if ls -a | grep -qE '\.tmp$'; then
  fail "a temporary publication file was left behind"
fi
true
