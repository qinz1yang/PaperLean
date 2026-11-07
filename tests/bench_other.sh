#!/usr/bin/env nix
#! nix develop ..#oldGlibc --command /usr/bin/env bash

set -euo pipefail
: "${RADAR_CACHE:?RADAR_CACHE must be set}"
: "${RADAR_OUT:?RADAR_OUT must be set}"

# This script must be called from the repo root.
# The radar environment variables must be provided.
# See also the https://github.com/leanprover/radar readme.

LLVM_RELEASE=23.1.0
LLVM_TARBALL="$RADAR_CACHE/llvm/$LLVM_RELEASE.tar.zst"

if [ ! -f "$LLVM_TARBALL" ] || [ ! -s "$LLVM_TARBALL" ]; then
    mkdir -p "$RADAR_CACHE/llvm"
    python3 - "$LLVM_TARBALL" "https://github.com/leanprover/lean-llvm/releases/download/$LLVM_RELEASE/lean-llvm-x86_64-linux-gnu.tar.zst" <<'PY'
import fcntl
import os
from pathlib import Path
import subprocess
import sys
import tempfile

archive = Path(sys.argv[1])
# Keep the lock inode stable so concurrent jobs see the same completed download.
with open(str(archive) + '.lock', 'a') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    if archive.is_file() and archive.stat().st_size > 0:
        sys.exit(0)
    with tempfile.TemporaryDirectory(dir=archive.parent, prefix=archive.name + '.tmp-') as directory:
        download = Path(directory) / 'download'
        subprocess.run(['curl', '--fail', '--location', '-o', str(download), sys.argv[2]], check=True)
        if not download.is_file() or download.stat().st_size == 0:
            sys.exit('LLVM archive download is empty')
        if not (archive.is_file() and archive.stat().st_size > 0):
            os.replace(download, archive)
PY
fi

mkdir -p build/release
cd build/release
# A command substitution inside eval would hide preparation's nonzero exit status.
LLVM_OPTIONS=$(../../script/prepare-llvm-linux.sh "$LLVM_TARBALL")
eval "cmake ../.. --preset release $LLVM_OPTIONS -DWFAIL=OFF"
rm -rf stage2
cp -r stage1 stage2
rm -rf stage3
cp -r stage1 stage3
cd ../..
# A successful command must produce this run's aggregate before it can be published.
rm -f tests/part2.measurements.jsonl
make -C build/release -j"$(nproc)" bench-part2
test -s tests/part2.measurements.jsonl
mv tests/part2.measurements.jsonl "$RADAR_OUT"
