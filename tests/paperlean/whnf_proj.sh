# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests the projections that `whnfCore` reduces by unfolding the structure (`Meta.whnfProj`): when
# `whnf` of the structure ends by unfolding a definition into a constructor application that it does
# not cache, only the projected field is instantiated. For each field of each instance of `Init`,
# `Std` and `Lean` that is a structure, applied to free variables (not cached) and to metavariables,
# at default and at instances transparency, `whnfCore` gives what projecting `whnf`'s result gives,
# while `PAPERLEAN_PROJ_ORACLE` compares each field so taken with the one of the full unfolding.

cat > "$TMP_DIR/WhnfProj.lean" <<'EOF2'
import Lean
open Lean Meta

/-- `whnfCore (.proj s i e)` as upstream's `whnfCore` computes it: from `whnf e`. -/
def reference (s : Name) (i : Nat) (e : Expr) : MetaM Expr := do
  let p := mkProj s i e
  let c ← match (← getConfig).proj with
    | .yesWithDeltaI => whnfAtMostI e
    | _ => whnf e
  match (← projectCore? c i) with
  | some f => whnfCore f
  | none => return p

run_meta do
  unless PaperLean.nativeAvailable (← getEnv) do
    throwError "PaperLean's native code is not available"
  let mut checked : Nat := 0
  let mut differ : Array Name := #[]
  for (c, info) in (← getEnv).constants.map₁.toList do
    unless info matches .defnInfo _ do continue
    unless (← isInstance c) do continue
    let us := info.levelParams.map mkLevelParam
    let r ← forallTelescope info.type fun xs ty => do
      let .const s _ := ty.getAppFn | return (0, #[])
      let some sinfo := getStructureInfo? (← getEnv) s | return (0, #[])
      let mut checked := 0
      let mut differ := #[]
      let mvars ← xs.mapM fun x => do mkFreshExprMVar (← inferType x)
      for args in [xs, mvars] do
        let e := mkAppN (mkConst c us) args
        for i in *...sinfo.fieldNames.size do
          for t in [TransparencyMode.default, .instances] do
            for proj in [ProjReductionKind.yesWithDelta, .yesWithDeltaI] do
              let same ← withTransparency t <| withConfig (fun cfg => { cfg with proj }) do
                let a ← try some <$> whnfCore (mkProj s i e) catch _ => pure none
                let b ← try some <$> reference s i e catch _ => pure none
                -- (`equal`: `==` does not see binder names and annotations)
                return match a, b with
                  | some a, some b => a.equal b
                  | none, none => true
                  | _, _ => false
              unless same do
                differ := differ.push c
              checked := checked + 1
      return (checked, differ)
    checked := checked + r.1
    differ := differ ++ r.2
  unless differ.isEmpty do
    throwError "different results for {differ.size} instances, e.g. {differ.toList.take 5}"
  unless checked > 10000 do
    throwError "too few projections checked: {checked}"
  logInfo "ok"
EOF2
cd "$TMP_DIR"
PAPERLEAN_PROJ_ORACLE=1 capture_exit 0 lean WhnfProj.lean
check_out_contains "ok"
check_out_matches "PAPERLEAN_PROJ_ORACLE: [0-9]*[0-9]{3} fields checked"

# A failed check must print the counterexample even inside a captured command.
cat > OracleMismatch.lean <<'EOF2'
module
import Lean
import all Lean.Meta.WHNF
open Lean Meta
run_meta do
  discard <| IO.FS.withIsolatedStreams <|
    Lean.Meta.checkProjOracle (mkNatLit 0) (mkNatLit 0) 0
EOF2
capture_exit 77 lean OracleMismatch.lean
check_out_contains "PAPERLEAN_PROJ_ORACLE: field 0"
check_out_contains "is none"
