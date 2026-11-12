# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# The flags with which `leanc` and Lake compile and link users' code (`Lean.Compiler.FFI.getCFlags'`,
# `getLinkerFlags'`) are official Lean's: PaperLean's build options (profile use, LTO, BOLT relocations,
# any CPU-specific code generation) are for the toolchain itself only, so a plain `lake build` of a user's
# executable generates official Lean's code.
OFFICIAL=${OFFICIAL_LEAN_TOOLCHAIN:-$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3}
[ -x "$OFFICIAL/bin/lean" ] || fail "official Lean 4.35.0-rc3 is not at $OFFICIAL (set OFFICIAL_LEAN_TOOLCHAIN to where it is)"
cd "$TMP_DIR"
cat > Flags.lean <<'END'
import Lean
#eval Lean.Compiler.FFI.getCFlags'
#eval Lean.Compiler.FFI.getLinkerFlags' true
#eval Lean.Compiler.FFI.getLinkerFlags' false
END
capture lean Flags.lean
cp "$CAPTURED.out.produced" paperlean.flags
capture env -u LEAN_PATH "$OFFICIAL/bin/lean" Flags.lean
$DIFF -- "$CAPTURED.out.produced" paperlean.flags || fail "users' compile or link flags differ from official Lean's"
grep -q 'march' paperlean.flags && fail "users' flags select a CPU"
true
