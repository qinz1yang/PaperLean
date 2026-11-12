#!/usr/bin/env python3
"""Writes a copy of an import image with one 4 KiB block of an extension's name/origin index
zeroed, so that the index slot(s) it holds read as zero. The block is chosen wholly inside the
index table (so no other table of the image is damaged) and to contain the home slot of a name or
origin that the image also has: the replay of an unpacked entry for it then probes a damaged zero
slot, which 0.2.3's `name_classes::get` / `origin_classes::find` take for an empty slot.

usage: import_image_index.py IMAGE HASHES {names|origins} OUT
  HASHES: lines "<i> <hash of ImgT.ti>" (the declarations of the packed module)
prints the choice and "use <i>"; exits 2 if no slot can be used.
"""
import struct
import sys
import os

HDR = 232          # sizeof(image_header)
REC = 272          # sizeof(image_ext)
BLOCK = 4096
M64 = (1 << 64) - 1
K = 0x9E3779B97F4A7C15


def u32(d, o):
    return struct.unpack_from("<I", d, o)[0]


def u64(d, o):
    return struct.unpack_from("<Q", d, o)[0]


def slot_of(h, size):
    return (((h * K) & M64) >> 20) & (size - 1)


def main():
    if len(sys.argv) != 5:
        print(__doc__)
        sys.exit(2)
    image, hashes, table, out = sys.argv[1:5]
    d = bytearray(open(image, "rb").read())
    num_exts = u32(d, 156)
    exts_off = u64(d, 184)
    simp = None
    for i in range(num_exts):
        b = exts_off + i * REC
        kind = u32(d, b + 16)
        nioff, ninum = u64(d, b + 168), u64(d, b + 176)
        if kind == 0 and ninum > 0:
            simp = b
            break
    if simp is None:
        print("no simp-set extension record", file=sys.stderr)
        sys.exit(2)
    names_off, names_num = u64(d, simp + 152), u64(d, simp + 160)
    nioff, ninum = u64(d, simp + 168), u64(d, simp + 176)
    ooff, onum = u64(d, simp + 184), u64(d, simp + 192)
    oioff, oinum = u64(d, simp + 200), u64(d, simp + 208)
    aoff, anum = u64(d, simp + 216), u64(d, simp + 224)
    eoff, enum = u64(d, simp + 232), u64(d, simp + 240)
    print(f"image={image} size={len(d)} simp record at {simp}: names=({names_off},{names_num}) "
          f"names_index=({nioff},{ninum}) origins=({ooff},{onum}) origins_index=({oioff},{oinum}) "
          f"arrays=({aoff},{anum}) entries=({eoff},{enum})")

    def usable(slot, off, num, elem):
        """The value at the slot is nonzero, and the block that holds it is wholly inside the table."""
        abs_ = off + slot * elem
        if not (off <= abs_ < off + num * elem):
            return None
        val = u32(d, abs_)
        blk = (abs_ - HDR) // BLOCK
        start = HDR + blk * BLOCK
        end = start + BLOCK
        if val == 0 or start < off or end > off + num * elem:
            return None
        return (abs_, val, start, end)

    if table == "names":
        hs = {}
        for line in open(hashes):
            i, h = line.split()
            hs[int(i)] = int(h)
        for i, h in sorted(hs.items()):
            slot = slot_of(h, ninum)
            c = usable(slot, nioff, ninum, 4)
            if c:
                abs_, val, start, end = c
                print(f"names: use t{i}, hash={h}, slot={slot}, abs={abs_}, class+1={val}, "
                      f"block=[{start},{end}) inside [{nioff},{nioff + ninum * 4})")
                chosen = i
                break
        else:
            print("no name slot in an interior block", file=sys.stderr)
            sys.exit(2)
    elif table == "origins":
        # The packed module has one entries array, in export order: entry i is theorem t<i>.
        arrays = []
        for j in range(anum):
            addr, first, count = u64(d, aoff + j * 16), u32(d, aoff + j * 16 + 8), u32(d, aoff + j * 16 + 12)
            if addr:
                arrays.append((addr, first, count))
        if len(arrays) != 1 or arrays[0][2] != 1024:
            print(f"expected one array of 1024 entries, got {arrays}", file=sys.stderr)
            sys.exit(2)
        _, first, count = arrays[0]
        for i in range(count):
            e = eoff + (first + i) * 56
            if d[e] != 0:            # .thm
                continue
            cls = u32(d, e + 24)
            if cls >= onum:
                continue
            key = u64(d, ooff + cls * 16)
            slot = slot_of(key, oinum)
            c = usable(slot, oioff, oinum, 4)
            if c:
                abs_, val, start, end = c
                print(f"origins: use t{i}, origin class={cls}, key={key}, slot={slot}, abs={abs_}, "
                      f"class+1={val}, block=[{start},{end}) inside [{oioff},{oioff + oinum * 4})")
                chosen = i
                break
        else:
            print("no origin slot in an interior block", file=sys.stderr)
            sys.exit(2)
    else:
        print("table must be names or origins", file=sys.stderr)
        sys.exit(2)

    mtime = struct.unpack_from("<q", d, 192)[0]
    nsec = struct.unpack_from("<q", d, 200)[0]
    blk = (abs_ - HDR) // BLOCK
    start = HDR + blk * BLOCK
    d[start:start + BLOCK] = b"\0" * BLOCK
    open(out, "wb").write(d)
    os.chmod(out, 0o644)
    os.utime(out, ns=(mtime * 10 ** 9 + nsec, mtime * 10 ** 9 + nsec))
    st = os.stat(out)
    assert st.st_mtime_ns // 10 ** 9 == mtime and st.st_mtime_ns % 10 ** 9 == nsec
    print(f"wrote {out}: block [{start},{start + BLOCK}) zeroed, mtime restored to {mtime}.{nsec:09d}")
    print(f"use {chosen}")


if __name__ == "__main__":
    main()
