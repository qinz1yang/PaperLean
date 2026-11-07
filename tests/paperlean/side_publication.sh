# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# The import image and native manifest writers are available on Darwin and Linux.
case "$(uname -s)" in Darwin|Linux) ;; *) return 0 ;; esac
unset LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS ELAN_TOOLCHAIN
driver="$(cd "$(dirname "$FILE")" && pwd -P)/side_publication.lean"
work="$(cd "$TMP_DIR" && pwd -P)/writers"
mkdir -p "$work/lib"
cd "$work"
echo 'theorem pubTiny (n : Nat) : n + 0 = n := Nat.add_zero n' > PubTiny.lean
lean -o "$work/lib/PubTiny.olean" PubTiny.lean || fail "failed to build publication input"
lean --run "$driver" pack "$work/lib" "$work/seed.pack" || fail "failed to pack publication input"
LEAN_PATH="$work/lib" LEAN_OLEAN_PACK="$work/seed.pack" python3 - "$driver" "$work" <<'PYTHON' ||
import subprocess
import sys
from pathlib import Path

driver, work = map(Path, sys.argv[1:])
for kind in ("manifest", "image"):
    for mode in ("hard", "symlink", "fifo", "nul", "race"):
        subprocess.run(["lean", "--run", driver, kind, mode, work / f"{kind}-{mode}"],
                       check=True, timeout=60)
PYTHON
  fail "native publication lost data, blocked, or left incomplete output"
