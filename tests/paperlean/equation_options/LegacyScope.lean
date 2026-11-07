module
public import LegacyWF
import Lean
open Lean Meta

private structure Snapshot where
  types : Bool
  replayed : Bool
  deepSplit : Bool
  deriving BEq, Hashable, TypeName

private def snapshot : MetaM Snapshot := do
  let opts ← getOptions
  return ⟨opts.get `backward.isDefEq.respectTransparency.types true,
          opts.get `backward.defeqAttrib.useBackward false,
          opts.get `backward.eqns.deepRecursiveSplit true⟩

set_option backward.isDefEq.respectTransparency.types false in
run_meta do
  let owner := ``Walk.legacyWF
  let outer ← withOptions (·.setBool `backward.eqns.deepRecursiveSplit false) <|
    withEqnOptions owner snapshot
  let inner ← realizeValue owner (Snapshot.mk true false false) (withEqnOptions owner snapshot)
  unless outer == ⟨false, true, true⟩ && inner == ⟨true, true, true⟩ do
    throwError "incorrect legacy option replay in the caller or the realization context"
