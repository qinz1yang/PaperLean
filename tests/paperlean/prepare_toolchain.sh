# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that what `paperlean prepare` decides does not depend on the `lean` of the `PATH`, as users run
# it: through the front end, in a project that keeps Lean's own toolchain, the `PATH` gives official Lean
# (here another toolchain's `lean`, and the real one and elan's where they are installed), or no `lean`.
# Lean's own code is that of the running `lean`: taken from any other, all of Lean counts as a package's,
# and a closed term that runs `Name.quickCmp` or reads a package's option is no longer known to be pure,
# which costs the native code of the module and of its importers. `LEAN_SYSROOT` does not change that.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN
ROOT="$(cd "$TMP_DIR" && pwd -P)"
mkdir -p "$ROOT/dep/Dep" "$ROOT/ws"
cd "$ROOT"
cat > dep/lakefile.toml <<'END'
name = "dep"
defaultTargets = ["Dep"]
[[lean_lib]]
name = "Dep"
END
cat > dep/Dep.lean <<'END'
import Dep.A
import Dep.B
import Dep.D
END
cat > dep/Dep/A.lean <<'END'
import Lean
open Lean
/-- A closed term that runs `Name.quickCmp`. -/
def Dep.names : NameSet := NameSet.empty.insert `a |>.insert `b
END
cat > dep/Dep/B.lean <<'END'
import Dep.A
def Dep.size : Nat := Dep.names.size
END
cat > dep/Dep/C.lean <<'END'
import Lean
register_option dep.flag : Bool := { defValue := true, descr := "an option of the package" }
END
cat > dep/Dep/D.lean <<'END'
import Dep.C
/-- A closed term that runs code on the value of an option. -/
def Dep.flagName : Lean.Name := dep.flag.name ++ `x
END
cat > ws/lakefile.toml <<'END'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "dep"
path = "../dep"
[[lean_lib]]
name = "Root"
END
printf 'import Dep\n#eval Dep.size\n' > ws/Root.lean
cd ws

capture lake paperlean --version
LEANVER=$(sed -n 's/.*-lean//p' "$CAPTURED.out.produced")
TC=$(dirname "$(dirname "$(command -v lake)")")
run lake build
echo "leanprover/lean4:v$LEANVER" > lean-toolchain
cp lean-toolchain ../dep/lean-toolchain

# The front end, with this toolchain as the PaperLean release for the project's Lean version.
export ELAN_HOME="$ROOT/elan"
mkdir -p "$ELAN_HOME/bin" "$ELAN_HOME/toolchains"
capture env ELAN_TOOLCHAIN=me/PaperLean:v0.1.0-lean$LEANVER lake paperlean install
ln -s "$TC" "$ELAN_HOME/toolchains/me--PaperLean---v0.1.0-lean$LEANVER"

# prepare <PATH> [variables]: what it prints, and the native modules that `lean` then uses
prepare() {
  local path=$1; shift
  rm -rf .lake/paperlean
  capture env PATH="$path" "$@" sh "$ELAN_HOME/bin/paperlean" prepare -j 2
  check_out_contains "Prepared"
  grep -E '^ +dep: |^ +e\.g\. ' "$CAPTURED.out.produced" | sed 's/ ([0-9ms]*)$//' > "$ROOT/decided"
  capture env PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake env lean Root.lean
  grep -o 'native libs=[0-9]* modules=[0-9]* meta=[0-9]* verified=[0-9]*' "$CAPTURED.out.produced" >> "$ROOT/decided"
}
same_as_paperlean() { # the case
  $DIFF "$ROOT/expected" "$ROOT/decided" || fail "with $1, prepare decides otherwise than with PaperLean first"
}

prepare "$TC/bin:/usr/bin:/bin"
cat "$ROOT/decided"
grep -q '^  dep: 5 modules$' "$ROOT/decided" || fail "the modules are not native with PaperLean first"
cp "$ROOT/decided" "$ROOT/expected"

# another toolchain's `lean`, as far as the question goes
mkdir -p "$ROOT/other/bin"
printf '#!/bin/sh\necho "%s"\n' "$ROOT/other" > "$ROOT/other/bin/lean"
chmod +x "$ROOT/other/bin/lean"
prepare "$ROOT/other/bin:/usr/bin:/bin"
same_as_paperlean "another toolchain's lean first"
prepare "/usr/bin:/bin"
same_as_paperlean "no lean"
prepare "$TC/bin:/usr/bin:/bin" LEAN_SYSROOT="$ROOT/other"
same_as_paperlean "LEAN_SYSROOT of another toolchain"

OFFICIAL="$HOME/.elan/toolchains/leanprover--lean4---v$LEANVER"
if [ -x "$OFFICIAL/bin/lean" ]; then
  prepare "$OFFICIAL/bin:/usr/bin:/bin"
  same_as_paperlean "official Lean first"
  if [ -x "$HOME/.elan/bin/lean" ]; then
    ln -s "$OFFICIAL" "$ELAN_HOME/toolchains/leanprover--lean4---v$LEANVER"
    prepare "$HOME/.elan/bin:/usr/bin:/bin"
    same_as_paperlean "elan's lean first"
  fi
fi
