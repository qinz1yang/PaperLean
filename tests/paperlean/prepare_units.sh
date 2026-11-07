# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests how `paperlean prepare` (`src/lake/Lake/PaperLean/Native.lean`) compiles a package's native
# library in units of modules: units are limited in size, two modules that define the same exported
# variable (never imported together) are not in one unit, where they would be one variable, so that
# the library cannot be linked, as when each is compiled on its own, a module whose `.c` file cannot
# be read is left out, and so is one that refers to a symbol that nothing defines. The library of the
# others loads then, whether what is left out holds functions or variables that they refer to, and
# they are used (with the package's symbol prefix): that of a module that declares an `@[extern]`
# function is interpreted.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN
WS="$(cd "$TMP_DIR" && pwd -P)/ws"
mkdir -p "$TMP_DIR/dep/Dep" "$WS/Root"
cat > "$TMP_DIR/dep/lakefile.toml" <<'END'
name = "dep"
defaultTargets = ["Dep"]
[[lean_lib]]
name = "Dep"
globs = ["Dep", "Dep.+"]
END
cat > "$TMP_DIR/dep/Dep.lean" <<'END'
import Dep.A
import Dep.B
import Dep.C
import Dep.D
END
cat > "$TMP_DIR/dep/Dep/C.lean" <<'END'
import Dep.A
@[extern "lean_paperlean_test_depc"] opaque depCExt : Nat → Nat
def depC (n : Nat) : Nat := n + depA
END
cat > "$TMP_DIR/dep/Dep/A.lean" <<'END'
def depA : Nat := 41
END
cat > "$TMP_DIR/dep/Dep/B.lean" <<'END'
import Dep.A
def depB : Nat := depA + 1
def bConst : Array Nat := (List.range 10).toArray.map (· * depA)
END
cat > "$TMP_DIR/dep/Dep/D.lean" <<'END'
import Dep.B
@[noinline] def useB (n : Nat) : Nat := bConst[n]! + 2
END
cat > "$WS/lakefile.toml" <<'END'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "dep"
path = "../dep"
[[lean_lib]]
name = "Root"
END
cat > "$WS/Root.lean" <<'END'
import Dep
def rootValue : Nat := depB + 1
END
cat > "$WS/Use.lean" <<'END'
import Dep
#eval depB
#eval depC 1
END
cd "$WS"
run lake build

capture lake paperlean prepare -j 2
check_out_contains "Compiling the native library of dep (2 jobs, 1 units)"
check_out_contains "dep: 5 modules"
NATIVE=$(ls -d "$PAPERLEAN_CACHE_DIR"/prepared/*/native/dep-*)
LIB=$(ls "$NATIVE"/dep.so "$NATIVE"/dep.dylib 2> /dev/null || true)
[ "$(stat -c %a "$LIB" 2>/dev/null || stat -f %Lp "$LIB")" = 555 ] || fail "the native library is not read-only"
[ -z "$(ls "$NATIVE"/*.rsp 2>/dev/null)" ] || fail "a response file was left"
capture env PAPERLEAN_UNIT_BYTES=1 lake paperlean prepare -j 2
check_out_contains "Compiling the native library of dep (2 jobs, 5 units)"
check_out_contains "dep: 5 modules"
capture lake lean Use.lean
printf '42\n42\n' | $DIFF -- - "$CAPTURED.out.produced" || fail "Use.lean differs from what Lean prints"
capture env PAPERLEAN_IMPORT_TIMING=1 env PAPERLEAN_ACCELERATE=1 lake lean Use.lean
check_out_contains "paperlean-timing native libs=1 modules=3 meta=0 verified=5 importsNotUsed=1 initOrder=0 other=1"
{ grep -v "^paperlean-" "$CAPTURED.out.produced" || true; } | $DIFF -- <(printf '42\n42\n') - ||
  fail "Use.lean differs with the native library"

# a `.c` file that cannot be read
chmod 000 "$TMP_DIR/dep/.lake/build/ir/Dep/B.c"
capture lake paperlean prepare -j 2
chmod 644 "$TMP_DIR/dep/.lake/build/ir/Dep/B.c"
check_out_contains "dep: 4 modules, 1 left out"
check_out_contains "Prepared"
# the module that reads a variable of the module left out is not used, and the others are
capture env PAPERLEAN_IMPORT_TIMING=1 PAPERLEAN_ACCELERATE=1 lake lean Use.lean
check_out_contains "paperlean-timing native libs=1 modules=1 "
! grep -q "ignoring native library" "$CAPTURED.out.produced" || fail "the library does not load"
{ grep -v "^paperlean-" "$CAPTURED.out.produced" || true; } | $DIFF -- <(printf '42\n42\n') - ||
  fail "Use.lean differs with a module left out"

# A module that refers to a symbol that nothing defines is left out and reported, with its reason.
cat > "$TMP_DIR/dep/Dep/E.lean" <<'END'
@[extern "lean_paperlean_test_missing"] opaque missing : Nat → Nat
END
cat > "$TMP_DIR/dep/Dep/F.lean" <<'END'
import Dep.E
def callsMissing (n : Nat) : Nat := missing n + 1
END
(cd "$TMP_DIR/dep" && run lake build Dep.E Dep.F)
capture lake paperlean prepare -j 2
check_out_contains "dep: 6 modules, 1 left out"
check_out_contains "e.g. Dep.F: it refers to lean_paperlean_test_missing, which nothing defines"
capture lake paperlean status
check_out_contains "native library of dep: 6 modules, 1 left out"
capture env PAPERLEAN_IMPORT_TIMING=1 PAPERLEAN_ACCELERATE=1 lake lean Use.lean
check_out_contains "paperlean-timing native libs=1 modules=3 "
! grep -q "ignoring native library" "$CAPTURED.out.produced" || fail "the library does not load"
rm "$TMP_DIR/dep/Dep/E.lean" "$TMP_DIR/dep/Dep/F.lean"
rm "$TMP_DIR"/dep/.lake/build/lib/lean/Dep/[EF].* "$TMP_DIR"/dep/.lake/build/ir/Dep/[EF].*

# Constants are evaluated to find out whether they panic: one that takes too long (a line names the
# module while it waits) or too much memory, or ends the process, makes its module interpreted, and the
# others are evaluated all the same. (The array is larger than what the allocator has reserved: the limit
# is on the address space. It does not hold on macOS, which does not enforce that.)
cat > "$TMP_DIR/dep/Dep/Spin.lean" <<'END'
partial def spin (n : Nat) : Nat := if n == 0 then spin 1 else spin (n + 1)
def spins : Nat := spin 0
END
cat > "$TMP_DIR/dep/Dep/Dies.lean" <<'END'
def dies : Nat := 2 ^ (2 ^ 70)
END
cat > "$TMP_DIR/dep/Dep/Late.lean" <<'END'
def late : Nat := "x".toNat!
END
cat > "$TMP_DIR/dep/Dep/Big.lean" <<'END'
def big : Nat := (Array.replicate 400000000 (0 : Nat)).size
END
(cd "$TMP_DIR/dep" && run lake build Dep.Spin Dep.Dies Dep.Late Dep.Big)
capture env PAPERLEAN_EVAL_MEMORY=64 lake paperlean prepare -j 2
check_out_contains "waiting for the constants of Dep.Spin (at most 10 s)"
check_out_contains "e.g. Dep.Spin: evaluating its constants takes more than 10 s"
check_out_contains "e.g. Dep.Dies: evaluating its constants ends the process"
check_out_contains "e.g. Dep.Late: "
# (`Dep.C`, its importer `Dep`, and these)
if [ "$(uname)" = Linux ]; then
  check_out_contains "dep: 9 modules, 6 interpreted"
  check_out_contains "e.g. Dep.Big: evaluating its constants ends the process, or takes more than 64 MiB"
else
  check_out_contains "dep: 9 modules, 5 interpreted"
fi
rm "$TMP_DIR"/dep/Dep/{Spin,Dies,Late,Big}.lean
rm "$TMP_DIR"/dep/.lake/build/lib/lean/Dep/{Spin,Dies,Late,Big}.* "$TMP_DIR"/dep/.lake/build/ir/Dep/{Spin,Dies,Late,Big}.*

# Two modules that are never imported together define the same exported variable.
cat > "$TMP_DIR/dep/Dep/V1.lean" <<'END'
initialize Shared.cfg : IO.Ref Nat ← IO.mkRef 1
def v1 : IO Nat := Shared.cfg.get
END
cat > "$TMP_DIR/dep/Dep/V2.lean" <<'END'
initialize Shared.cfg : IO.Ref Nat ← IO.mkRef 2
def v2 : IO Nat := Shared.cfg.get
END
(cd "$TMP_DIR/dep" && run lake build Dep.V1 Dep.V2)
capture lake paperlean prepare -j 2
check_out_contains "Compiling the native library of dep (2 jobs, 2 units)"
# Some host linkers coalesce tentative variables; others reject the duplicate symbol.
# If linking succeeds, both conflicting definitions must still be interpreted.
if ! grep -q "the native library of dep could not be built" "$CAPTURED.out.produced"; then
  check_out_contains 'e.g. Dep.V1: `Shared.cfg` runs `Shared.cfg`, which modules define differently'
  check_out_contains 'e.g. Dep.V2: `Shared.cfg` runs `Shared.cfg`, which modules define differently'
fi
for version in 1 2; do
  cat > "UseV$version.lean" <<END
import Dep.V$version
#eval v$version
END
  capture lake lean "UseV$version.lean"
  printf '%s\n' "$version" | $DIFF -- - "$CAPTURED.out.produced" || fail "conflicting variable baseline differs"
  capture env PAPERLEAN_ACCELERATE=1 lake lean "UseV$version.lean"
  printf '%s\n' "$version" | $DIFF -- - "$CAPTURED.out.produced" || fail "conflicting variable ran natively"
done
