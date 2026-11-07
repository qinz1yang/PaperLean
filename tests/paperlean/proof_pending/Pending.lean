/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PendingTools

open ProofBase
universe u

#hold_predecessor
theorem pendingVia {α : Type u} (x : α) (n : Nat) : Holds (target x n) := witness x n
#observe_then_release pendingVia
#finish_predecessor pendingVia

-- This declaration has the exact same type and proof as the one above, with every predecessor checked.
theorem readyVia {α : Type u} (x : α) (n : Nat) : Holds (target x n) := witness x n
#compare_ready pendingVia readyVia
example : @pendingVia = @readyVia := rfl
#print axioms pendingVia
#print axioms readyVia
