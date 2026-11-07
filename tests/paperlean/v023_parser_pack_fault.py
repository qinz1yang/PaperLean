# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
from pathlib import Path
import struct
import sys

root = Path(sys.argv[1])
# A relocated compact string's capacity remains valid for the region walk. Its corrupt
# byte count must never be used to read beyond its payload while building a parser hint.
def set_byte_count(path, marker, count):
    data = bytearray(path.read_bytes())
    needle = marker + b"\0"
    assert data.count(needle) == 1
    pos = data.index(needle) - 3 * struct.calcsize("P")
    assert int.from_bytes(data[pos:pos+8], sys.byteorder) == len(needle)
    data[pos:pos+8] = count.to_bytes(8, sys.byteorder)
    path.write_bytes(data)


set_byte_count(root / "Malformed.olean", b"paperlean-parser-hint-fixture", 2**64 - 1)
# The stock trie sees a one-byte string after boxing the length. Hashing the full
# advertised size would read past the allocation before the next (invalid) parser.
for path, token in [(root / "Wrapped.olean", b"a-wrapped-packed"),
                    (root.parent / "loose" / "LooseBad.olean", b"a-wrapped-loose")]:
    set_byte_count(path, token, 2**63 + 2)

# Same target's v2 fixed header, followed by the v3 length and closure-count fields.
# Neither a missing root pointer nor a wrapped section length is eligible for packing.
header = bytearray((root / "Dense.olean").read_bytes()[:88])
assert header[:6] == b"olean\x02" and struct.calcsize("P") == 8
header[5] = 3
for name, declared, payload in [("TooShort", 1, b"x"), ("Wrap", 2**64 - 1, b"")]:
    (root / (name + ".olean")).write_bytes(
        header + declared.to_bytes(8, sys.byteorder) + payload + bytes(4)
    )
