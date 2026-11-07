module
import Lean
open Lean Meta

set_option backward.isDefEq.respectTransparency.types false in
def auditWF (n : Nat) : Nat :=
  if h : n = 0 then 0 else auditWF (n - 1)
termination_by n

private structure Snapshot where
  setting : Bool
  deriving BEq, Hashable, TypeName

-- Both the equation type and its proof may consult the first realization snapshot.
run_meta do
  let n := ``auditWF
  let key := `backward.isDefEq.respectTransparency.types
  let outer ← withEqnOptions n do pure <| (← getOptions).get key true
  let inner : Snapshot ← realizeValue n (Snapshot.mk true) <| withEqnOptions n do
    pure ⟨(← getOptions).get key true⟩
  if outer || inner.setting then throwError "lost the unary WF definition's transparency option"
