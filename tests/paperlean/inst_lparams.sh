# Tests `Lean.Expr.instantiateLevelParams` in native code (`src/paperlean/inst_lparams.cpp`): for the
# types and values of the constants of `Init`, `Std` and `Lean` that have universe parameters, it
# gives the same expressions as Lean's traversal (`instantiateLevelParamsArray`), with the parameters
# instantiated by other universes and by too few of them.

cat > "$TMP_DIR/InstLParams.lean" <<'EOF2'
import Lean
open Lean

run_cmd do
  unless PaperLean.nativeAvailable (← getEnv) do
    throwError "PaperLean's native code is not available"
  let mut checked : Nat := 0
  let mut differ : Array Name := #[]
  for (c, info) in (← getEnv).constants.map₁.toList do
    let ps := info.levelParams
    if ps.isEmpty then continue
    let us := ps.mapIdx fun i _ => if i % 2 == 0 then mkLevelMax (mkLevelParam `w) (.succ .zero) else .zero
    for e in [info.type] ++ info.value?.toList do
      for us in [us, us.take 1] do
        checked := checked + 1
        unless e.instantiateLevelParams ps us == e.instantiateLevelParamsArray ps.toArray us.toArray do
          differ := differ.push c
  unless differ.isEmpty do
    throwError "different results for {differ.size} constants, e.g. {differ.toList.take 5}"
  unless checked > 100000 do
    throwError "too few expressions checked: {checked}"
  logInfo "ok"
EOF2
cd "$TMP_DIR"
capture_exit 0 lean InstLParams.lean
check_out_contains "ok"
