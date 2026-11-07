# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Inject a missing library into a validated, native-format v3 cleanup fixture."""

import bisect
from pathlib import Path
import struct
import sys


MISSING_LIBRARY = b"__paperlean_region_cleanup_missing_library__"
HEADER_SIZE = 88
DATA_OFFSET = HEADER_SIZE + 8
BYTE_ORDER = "<" if sys.byteorder == "little" else ">"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def parse(data):
    # These are the same native 64-bit header offsets used by region_probe.c.
    require(struct.calcsize("P") == 8, "the fixture requires a 64-bit host")
    require(len(data) >= DATA_OFFSET, "truncated header")
    require(data[:6] == b"olean\x03", "expected a v3 compacted region")
    require(data[6] & ~1 == 0, "unknown header flags")

    def word(offset, code):
        size = struct.calcsize(code)
        require(0 <= offset <= len(data) - size, "truncated metadata")
        return struct.unpack_from(BYTE_ORDER + code, data, offset)[0]

    base = word(80, "Q")
    require(base != 0 and base % 65536 == 0, "invalid preferred base")
    size = word(HEADER_SIZE, "Q")
    require(size >= 8 and size % 8 == 0, "invalid data size")
    end = DATA_OFFSET + size
    require(end <= len(data) - 4, "truncated compacted data")
    count = word(end, "I")
    pos = end + 4
    require(0 < count <= (len(data) - pos) // 8, "invalid closure count")
    offsets = [word(pos + 8 * i, "Q") for i in range(count)]
    require(len(set(offsets)) == count, "duplicate closure offsets")
    require(all(8 <= off <= size - 8 and off % 8 == 0 for off in offsets),
            "invalid closure offset")
    pos += count * 8
    count = word(pos, "I")
    pos += 4
    require(0 < count <= len(offsets), "invalid library count")
    libraries = []
    for _ in range(count):
        lib_base = word(pos, "Q")
        length_pos = pos + 8
        length = word(length_pos, "I")
        pos += 12
        require(length <= len(data) - pos, "truncated library identity")
        identity = data[pos:pos + length]
        require(b"\0" not in identity, "invalid loader identity")
        libraries.append((lib_base, identity, length_pos, pos + length))
        pos += length
    require(pos == len(data), "unexpected trailing data")
    bases = [lib[0] for lib in libraries]
    require(bases == sorted(set(bases)), "unsorted or duplicate library bases")
    owners = {bisect.bisect_right(bases, word(DATA_OFFSET + off, "Q")) - 1
              for off in offsets}
    require(owners == set(range(len(libraries))), "inconsistent used-library table")
    return end, offsets, libraries


def inject(data, payload_size):
    end, offsets, libraries = parse(data)
    require(payload_size > 0, "expected a positive payload size")
    require(payload_size <= end - DATA_OFFSET, "captured payload is too small")
    require(data.find(bytes([37]) * payload_size, DATA_OFFSET, end) >= 0,
            "captured payload is missing")
    require(all(lib[1] != MISSING_LIBRARY for lib in libraries),
            "missing-library marker already present")
    _, _, start, stop = libraries[0]
    replacement = struct.pack(BYTE_ORDER + "I", len(MISSING_LIBRARY)) + MISSING_LIBRARY
    changed = data[:start] + replacement + data[stop:]
    new_end, new_offsets, new_libraries = parse(changed)
    require(new_end == end and changed[:end] == data[:end], "compacted data changed")
    require(new_offsets == offsets, "closure offsets changed")
    expected = [(lib[0], MISSING_LIBRARY if i == 0 else lib[1])
                for i, lib in enumerate(libraries)]
    require([(lib[0], lib[1]) for lib in new_libraries] == expected,
            "unexpected library metadata change")
    return changed


def main():
    require(len(sys.argv) == 4, "expected input, output and captured byte count")
    source, target = map(Path, sys.argv[1:3])
    changed = inject(source.read_bytes(), int(sys.argv[3]))
    # Keep the successful original fixture intact; never overwrite an existing output.
    with target.open("xb") as out:
        out.write(changed)


if __name__ == "__main__":
    main()
