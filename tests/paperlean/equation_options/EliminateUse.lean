module
public import Eliminate
import Lean
namespace V
section
variable {n} {a b : V (n+1)} (f : Arr (drop a) (drop b)) (g : V.last a → V.last b)
example (i : Ix n) : choose f g (.succ i) = f i := by rw [choose.eq_1]
example : choose f g .zero = g := by rw [choose.eq_2]
example (i : Ix n) : chooseAgain f g (.succ i) = f i := by rw [chooseAgain.eq_1]
example : chooseAgain f g .zero = g := by rw [chooseAgain.eq_2]
end
section
variable {n} (a : V n) {β γ : Type} (r : β → γ → Prop)
example (i : Ix n) : @chooseRel n a β γ r (.succ i) = Eq := by rw [chooseRel.eq_1]
example : @chooseRel n a β γ r .zero = r := by rw [chooseRel.eq_2]
end
end V

open Lean in
run_meta do
  for (n, arity) in [(``V.choose.eq_1, 6), (``V.choose.eq_2, 5),
      (``V.chooseAgain.eq_1, 6), (``V.chooseAgain.eq_2, 5),
      (``V.chooseRel.eq_1, 6), (``V.chooseRel.eq_2, 5)] do
    unless (← getConstInfo n).type.getForallArity == arity do
      throwError "unexpected arity for {n}"
