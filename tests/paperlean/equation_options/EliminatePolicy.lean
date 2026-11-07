module
public import Eliminate
import Lean
open Lean Meta
run_meta do
  let env ← getEnv
  let [one, two] ← [``V.choose, ``V.chooseAgain].mapM getConstInfoDefn | unreachable!
  let head := one.value.getLambdaBody.getAppFn
  unless head == two.value.getLambdaBody.getAppFn && head.constName!.getPrefix == ``V.choose &&
      (isMatcherAppCore? env one.value.getLambdaBody).isSome do
    throwError "expected both declarations to reuse the first declaration's matcher"
  let mode ← IO.getEnv "PAPERLEAN_TEST_EQUATION_TYPES"
  let check (n : Name) (expected : Bool) : MetaM Unit := do
    let settings := (eqnOptionsExt.find? env n).getD #[]
    unless settings.contains (`backward.isDefEq.respectTransparency, DataValue.ofBool true) &&
        settings.contains (`backward.isDefEq.respectTransparency.types, DataValue.ofBool expected) do
      throwError "incorrect producer policy for {n}: {settings}"
  for n in [``V.choose, ``V.chooseAgain, ``V.chooseRel, ``V.chooseGlobal, ``V.chooseNamedGlobal, ``V.chooseId] do
    check n (mode == some "true")
  for n in [``V.choosePred, ``V.chooseType, ``V.chooseConst, ``V.chooseLocalId] do
    check n true
