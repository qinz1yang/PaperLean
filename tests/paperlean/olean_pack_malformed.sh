# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# `OLeanPack.create` must leave out a chain whose `.olean` is not the module data that the pack
# tables assume, like it leaves out one with an unreadable or changed file. A header-valid `.olean`
# whose `ModuleData.imports` (field 0) or `constNames` (field 1) is a scalar used to make the writer
# dereference the scalar as an array (SIGSEGV); a truncated or overflowing array/string header made
# the region reader walk past the region before the writer could check the root. Creation must pack
# the valid chain and leave the malformed ones to be read from disk.
case "$(uname -s)" in Linux|Darwin) ;; *) return 0 ;; esac
unset LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS PAPERLEAN_IMPORT 2>/dev/null || true
ROOT="$TMP_DIR/malformed-pack"
mkdir -p "$ROOT/root" "$ROOT/lib"
cd "$ROOT"
printf 'def packedGood : Nat := 7\n' > Good.lean
run lean -o lib/Good.olean Good.lean
cp lib/Good.olean root/Good.olean
python3 - <<'PY'
from pathlib import Path
import struct

good = Path('root/Good.olean').read_bytes()
version = good[5]
root_slot = 88 if version == 2 else 96
base = int.from_bytes(good[80:88], 'little')
root = int.from_bytes(good[root_slot:root_slot + 8], 'little')
root_off = root - base
assert 0 <= root_off < len(good) - 8, (version, base, root, len(good))

def write(name, data):
    Path('root/' + name + '.olean').write_bytes(data)

# `ModuleData`'s object fields start after the object header: imports is field 0 (+8) and
# constNames is field 1 (+16). A scalar in either is malformed data, not a packable object.
for name, field in (('BadImports', 0), ('BadConstNames', 1)):
    b = bytearray(good)
    off = root_off + 8 + 8 * field
    assert 0 <= off <= len(b) - 8, (name, version, base, root, len(b))
    b[off:off + 8] = (1).to_bytes(8, 'little')
    write(name, b)

const_names = int.from_bytes(good[root_off + 16:root_off + 24], 'little')
array_off = const_names - base
assert 0 <= array_off + 24 <= len(good) - 8, (array_off, len(good))
# `lean_array_object.m_size` names far more elements than the array's capacity.
b = bytearray(good)
b[array_off + 8:array_off + 16] = (0xffffffff).to_bytes(8, 'little')
write('ZBadArraySize', b)
# A capacity that overflows the object size computation.
b = bytearray(good)
b[array_off + 16:array_off + 24] = (0xffffffffffffffff).to_bytes(8, 'little')
write('ZBadArrayCapacity', b)

# The root slot points outside the region; the reader must reject it, not call `lean_unreachable`.
b = bytearray(good)
b[root_slot:root_slot + 8] = (base + 0x100000).to_bytes(8, 'little')
write('ZBadRoot', b)

# The first string of the first `Name.str` of `constNames` advertises an impossible capacity.
first_name = int.from_bytes(good[array_off + 24:array_off + 32], 'little')
name_off = first_name - base
if 0 <= name_off + 24 <= len(good) - 8 and good[name_off + 7] == 1:
    string = int.from_bytes(good[name_off + 16:name_off + 24], 'little')
    string_off = string - base
    if 0 <= string_off + 32 <= len(good) - 8:
        b = bytearray(good)
        b[string_off + 16:string_off + 24] = (0xffffffffffffffff).to_bytes(8, 'little')
        write('ZBadStringCapacity', b)

if version == 2:
    # Append only the first 8 bytes of a real LeanArray header: the region ends inside the
    # header, before the fields that `lean_object_byte_size`/`fix_array` read.
    b = good + good[array_off:array_off + 8]
    write('ZBadTruncatedArray', b)
PY
cat > pack.lean <<'LEAN'
import Lean.PaperLean.OLeanPack
def main (args : List String) : IO UInt32 := do
  try
    let n ← Lean.PaperLean.OLeanPack.create #[args[0]!] args[1]!
    IO.println s!"packed {n}"
    let why ← Lean.PaperLean.OLeanPack.verify args[1]!
    unless why.isEmpty do throw <| IO.userError why
    return 0
  catch e =>
    IO.eprintln s!"create failed: {e}"
    return 1
LEAN
# On the current toolchain this crashes (SIGSEGV) or reports a malformed chain as an error.
capture lean --run pack.lean "$ROOT/root" "$ROOT/out.paperlean"
check_out_contains "packed 1"
cat > Use.lean <<'LEAN'
import Good
import Lean.PaperLean.OLeanPack
#eval packedGood
#eval show IO Unit from do
  let (served, _) ← Lean.PaperLean.OLeanPack.stats
  IO.println s!"served {served}"
LEAN
capture env LEAN_PATH="$ROOT/root" LEAN_OLEAN_PACK="$ROOT/out.paperlean" lean Use.lean
check_out_contains "7"
check_out_contains "served 1"
