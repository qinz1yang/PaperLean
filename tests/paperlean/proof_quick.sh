# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests `Meta.isProofQuick` (`Lean.Meta.InferType`), which decides on the type of a constant with
# its universe parameters where that decides it for every instantiation: its answers for every
# constant of `Init`, with parameters, zeros and ones as levels and applied to several numbers of
# arguments, are official Lean's (the expected digest is official Lean 4.35.0-rc3's).

cat > "$TMP_DIR/ProofQuick.lean" <<'EOF2'
import Lean
open Lean Meta

/-! `isProofQuick` of every constant of `Init`, with universe parameters, zeros and ones as levels,
applied to 0 to 3 arguments and to as many as its type has binders: counts of the answers and a
digest of them, to compare with official Lean's. -/

run_meta do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      if env.header.moduleNames[idx]!.getRoot == `Init then
        names := names.push n
  names := names.qsort Name.quickLt
  let mut digest : UInt64 := 7
  let mut counts : Array Nat := #[0, 0, 0]
  for n in names do
    let some ci := env.find? n | continue
    let ps := ci.levelParams
    let binders := ci.type.getForallBinderNames.length
    for us in [ps.map mkLevelParam, ps.map fun _ => .zero, ps.map fun _ => .succ .zero] do
      for arity in [0, 1, 2, 3, binders] do
        let e := mkAppN (.const n us) (.replicate arity (mkConst ``Nat.zero))
        let r ← isProofQuick e
        let i := match r with | .false => 0 | .true => 1 | .undef => 2
        counts := counts.modify i (· + 1)
        digest := mixHash digest (mixHash (hash n) (hash (arity * 3 + i)))
  logInfo m!"{names.size} constants, false/true/undef {counts}, digest {digest}"
EOF2
cd "$TMP_DIR"
lean ProofQuick.lean > proof_quick.out 2>&1 || fail "ProofQuick.lean failed: $(cat proof_quick.out)"
echo "65972 constants, false/true/undef [138612, 622771, 228197], digest 8027908856257154066" |
  $DIFF -- - proof_quick.out || fail "isProofQuick answers otherwise than Lean"
