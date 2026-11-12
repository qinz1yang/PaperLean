# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# `Float` results must be bit-identical to official Lean's, also when the toolchain's C/C++ is compiled
# for CPUs with fused multiply-add (e.g. `-march=x86-64-v3`): neither Lean's own C/C++ (runtime, the
# compiled standard library) nor users' code compiled by `leanc` may contract `x * y + z` into an FMA
# (`-ffp-contract=off`). With
# a = 1 + 2^-27 and c = -(1 + 2^-26), a * a + c is 0 when rounded twice and 2^-54 when fused. Interpreted
# (`#eval`), through compiled library functions, and in an executable compiled by `leanc`, the output must
# equal official Lean 4.35.0-rc3's.
OFFICIAL=${OFFICIAL_LEAN_TOOLCHAIN:-$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3}
[ -x "$OFFICIAL/bin/lean" ] || fail "official Lean 4.35.0-rc3 is not at $OFFICIAL (set OFFICIAL_LEAN_TOOLCHAIN to where it is)"
cd "$TMP_DIR"
cat > F.lean <<'END'
@[noinline] def mulAdd (x y z : Float) : Float := x * y + z
@[noinline] def mulSub (x y z : Float) : Float := x * y - z
def a : Float := Float.ofBits 0x3FF0000002000000
def c : Float := Float.ofBits 0xBFF0000004000000
def results : List String := [
  s!"mulAdd {(mulAdd a a c).toBits}",
  s!"mulSub {(mulSub a a (-c)).toBits}",
  s!"inline {(a * a + c).toBits}",
  s!"ofScientific {(Float.ofScientific 123456789012345678 true 37).toBits}",
  s!"sum {((0.1 : Float) + 0.2).toBits} {(0.1 : Float) + 0.2}",
  s!"sqrt {(Float.sqrt 2.0).toBits} exp {(Float.exp 1.0).toBits} log {(Float.log 10.0).toBits}",
  s!"pow {(Float.pow 1.0000001 1000000.0).toBits} sin {(Float.sin 1e10).toBits}",
  s!"toString {(1.0 / 3.0 : Float)} {(2.0 / 3.0 : Float)} {(1e-300 * 1e-10 : Float)}",
  s!"poly {((List.range 50).foldl (fun acc i => acc * a + (Float.ofNat i) * c) 0.0).toBits}"]
#eval results
def main : IO Unit := results.forM IO.println
END
capture lean F.lean
cp "$CAPTURED.out.produced" paperlean.eval
grep -q 'mulAdd 0' paperlean.eval || fail "a * a + c is not 0: the multiplication and the addition were fused"
capture env -u LEAN_PATH "$OFFICIAL/bin/lean" F.lean
cp "$CAPTURED.out.produced" official.eval
$DIFF -- official.eval paperlean.eval || fail "interpreted Float results differ from official Lean's"
run lean -c F.c F.lean
run leanc F.c -o f
capture ./f
cp "$CAPTURED.out.produced" paperlean.exe
grep -q '^mulAdd 0$' paperlean.exe || fail "the compiled executable fused a * a + c"
run env -u LEAN_PATH "$OFFICIAL/bin/lean" -c Fo.c F.lean
run env -u LEAN_PATH "$OFFICIAL/bin/leanc" Fo.c -o fo
capture ./fo
$DIFF -- "$CAPTURED.out.produced" paperlean.exe || fail "compiled Float results differ from official Lean's"
true
