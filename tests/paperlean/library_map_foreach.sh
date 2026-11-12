# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# `smap_foreach` must iterate a current `Lean.SMap`: its object fields are `map₁` (a `Std.HashMap`,
# at run time `(size, buckets)`) and `map₂` (a `PHashMap`, whose root is its entries array; `stage₁` is
# a scalar). On the unfixed library the persistent map's visitor takes that array for a collision node
# and the executable aborts (assertion) or crashes.

WS="$TMP_DIR/library-map-foreach"
mkdir -p "$WS"
cd "$WS"
cat > Smap.lean <<'LEAN'
import Lean
open Lean
@[extern "lean_smap_foreach_test"] opaque foreachTest (m : SMap Nat Bool) : Nat
def main : IO Unit := do
  let mut m : SMap Nat Bool := {}
  m := m.insert 1 true
  m := m.insert 2 false
  m := m.switch
  m := m.insert 3 true
  IO.println (foreachTest m)
LEAN
run lean -c Smap.c -Dcompiler.postponeCompile=false Smap.lean
run leanc Smap.c -o smap
capture ./smap
[ "$(grep -c '>> ' "$CAPTURED.out.produced")" -eq 3 ] || fail "not all SMap entries were visited"
true
