# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# A pack of the cache is written by a process that maps it at the address range that the cache reserves
# for it, and that has mapped files where they ask to be: the `.olean` files of the modules that loading
# the workspace imported, at addresses that Lean derives from the modules' names (about 40% of Lean's
# own lie in the range where the cache reserves packs). A reserved range in which the writer has
# something mapped cannot be written ("address range at ... is not available"), and `paperlean prepare`
# failed in the same way every time; for a pack of the whole of Mathlib, about one cache layout in eight.
# On Linux, with a C compiler: a library preloaded into every process maps the range that the cache
# reserves first; `paperlean prepare` must still write its pack elsewhere, and Lean must use it.
[ "$(uname -s)" = Linux ] || exit 0
unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN
ROOT="$(cd "$TMP_DIR" && pwd -P)"
cd "$ROOT"
cat > mapat.c <<'END'
#define _GNU_SOURCE
#include <fcntl.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <unistd.h>
#ifndef MAP_FIXED_NOREPLACE
#define MAP_FIXED_NOREPLACE 0x100000
#endif
/* `Lake.PaperLean.Cache.slotsStart`, `slotAlign` bytes: the range that an empty cache reserves first */
__attribute__((constructor)) static void map_first_slot(void) {
    void * want = (void *)0x400000000000UL;
    void * m = mmap(want, 1UL << 30, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE | MAP_FIXED_NOREPLACE, -1, 0);
    char const * log = getenv("MAPAT_LOG");
    if (m == want && log) {
        int fd = open(log, O_WRONLY | O_CREAT | O_APPEND, 0644);
        if (fd >= 0) { static const char msg[] = "active\n"; ssize_t r = write(fd, msg, sizeof msg - 1); (void)r; close(fd); }
    }
}
END
if ! ${CC:-cc} -shared -fPIC -O1 -o mapat.so mapat.c > cc.log 2>&1; then
  echo "skipping: no C compiler for the LD_PRELOAD library ($(head -1 cc.log))"
  exit 0
fi

mkdir -p ws/dep/Dep
cd ws
cat > dep/lakefile.toml <<'END'
name = "dep"
defaultTargets = ["Dep"]
[[lean_lib]]
name = "Dep"
END
printf 'def base (n : Nat) : Nat := n + 1\n' > dep/Dep/Base.lean
cat > dep/Dep/Twice.lean <<'END'
import Lean
macro "twice! " x:term : term => `($x + $x)
END
printf 'import Dep.Base\nimport Dep.Twice\n' > dep/Dep.lean
cat > lakefile.toml <<'END'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "dep"
path = "dep"
[[lean_lib]]
name = "Root"
END
printf 'import Dep\n#eval twice! base 20\n' > Root.lean
run lake build Dep
capture lake lean Root.lean
cp "$CAPTURED.out.produced" "$ROOT/plain.out"

capture env LD_PRELOAD="$ROOT/mapat.so" MAPAT_LOG="$ROOT/mapat.log" lake paperlean prepare -j 2
check_out_contains "Packing dep"
grep -q active "$ROOT/mapat.log" || fail "the preloaded library did not map the range"
python3 - "$PAPERLEAN_CACHE_DIR" <<'END'
import glob, json, sys
slots = [s for f in glob.glob(sys.argv[1] + "/**/slots.json", recursive=True) for s in json.load(open(f))]
assert slots, "the cache reserved no address range"
lo, hi = 0x400000000000, 0x400000000000 + (1 << 30)
bad = [s for s in slots if s["base"] < hi and lo < s["base"] + s["size"]]
assert not bad, f"a pack was put where its writer had something mapped: {bad}"
END

# Lean uses the pack, with that range mapped in it as well, as many of its modules as without, and the
# output is the same. (No native code: a preloaded library is an input of native code that prepared
# data does not record, so `prepare` leaves the native library out.)
served() { sed -n 's/^paperlean-timing modules.fast packed=\([0-9]*\) .*/\1/p' "$CAPTURED.out.produced"; }
capture env PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean Root.lean
plain_served=$(served)
[ -n "$plain_served" ] && [ "$plain_served" -gt 0 ] || fail "the packs served no module"
capture env LD_PRELOAD="$ROOT/mapat.so" PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean Root.lean
! grep -q "^warning: ignoring olean pack" "$CAPTURED.out.produced" || fail "the pack is not used: $(grep "^warning" "$CAPTURED.out.produced")"
[ "$(served)" = "$plain_served" ] || fail "the packs served $(served) modules with the range mapped, $plain_served without"
{ grep -v "^paperlean-\|^warning: " "$CAPTURED.out.produced" || true; } | $DIFF -- "$ROOT/plain.out" - ||
  fail "the prepared data changes the output"
