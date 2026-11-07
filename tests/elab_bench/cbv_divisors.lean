import Lean
open Lean

def divisorsList (n : Nat) : List Nat :=
  (List.range' 1 n).filter fun d => n % d = 0

def mkProblem (n : Nat) : Expr := mkApp (mkConst ``divisorsList) (mkNatLit n)

/-- Decode only syntactic Nat literals, constructors, and the canonical Nat OfNat form. -/
partial def readNatNormalForm (e : Expr) : Option Nat := do
  let e := e.consumeMData
  if let some n := e.rawNatLit? then
    return n
  else if e == mkConst ``Nat.zero then
    return 0
  else if e.isAppOfArity ``Nat.succ 1 && e.getAppFn == mkConst ``Nat.succ then
    return (← readNatNormalForm (e.getArg! 0)) + 1
  else if e.isAppOfArity ``OfNat.ofNat 3 &&
      e.getAppFn == mkConst ``OfNat.ofNat [.zero] &&
      (e.getArg! 0).consumeMData == mkConst ``Nat then
    let some n := (e.getArg! 1).consumeMData.rawNatLit? | none
    let inst := (e.getArg! 2).consumeMData
    if inst.isAppOfArity ``instOfNatNat 1 && inst.getAppFn == mkConst ``instOfNatNat &&
        (inst.getArg! 0).consumeMData.rawNatLit? == some n then
      return n
    else
      none
  else
    none

private def natOfNatExpr (n : Nat) : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Nat) (mkRawNatLit n)
    (mkApp (mkConst ``instOfNatNat) (mkRawNatLit n))

-- These checks reject reducible arithmetic and malformed/custom numeral instances.
#guard readNatNormalForm (mkRawNatLit 7) == some 7
#guard readNatNormalForm (mkConst ``Nat.zero) == some 0
#guard readNatNormalForm (mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)) == some 1
#guard readNatNormalForm (natOfNatExpr 1) == some 1
#guard readNatNormalForm (mkApp (mkConst ``Nat.succ) (natOfNatExpr 2)) == some 3
#guard readNatNormalForm (mkApp2 (mkConst ``Nat.add) (mkRawNatLit 0) (mkRawNatLit 1)) == none
#guard readNatNormalForm (mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Int)
  (mkRawNatLit 1) (mkApp (mkConst ``instOfNatNat) (mkRawNatLit 1))) == none
#guard readNatNormalForm (mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Nat)
  (mkRawNatLit 1) (mkApp (mkConst ``instOfNatNat) (mkRawNatLit 2))) == none
#guard readNatNormalForm (mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Nat)
  (mkRawNatLit 1) (mkConst ``Nat.zero)) == none

/-- Read a complete syntactic normal form, without reducing or proving it equal to the input. -/
partial def readNatList (e : Expr) : Option (List Nat) := do
  let e := e.consumeMData
  if e.isAppOfArity ``List.nil 1 && e.getArg! 0 == mkConst ``Nat then
    return []
  else if e.isAppOfArity ``List.cons 3 && e.getArg! 0 == mkConst ``Nat then
    let head ← readNatNormalForm (e.getArg! 1)
    return head :: (← readNatList (e.getArg! 2))
  else
    none

def runProblem (n : Nat) : MetaM Unit := do
  let problem := mkProblem n
  let startTime ← IO.monoNanosNow
  let executed ← Lean.Meta.Tactic.Cbv.cbvEntry problem
  let endTime ← IO.monoNanosNow
  let ms := (endTime - startTime).toFloat / 1000000.0
  -- Correctness checking is deliberately outside both measured regions.
  let some actual := readNatList (executed.getResultExpr problem)
    | throwError "CBV did not produce a complete List Nat normal form for {n}"
  let expected := (List.range n).filterMap fun i => if n % (i + 1) == 0 then some (i + 1) else none
  unless actual == expected do
    throwError "incorrect CBV normal form for {n}: {actual}; expected {expected}"
  match executed with
  | .rfl _ _ => IO.println s!"goal_{n}: {ms} ms"
  | .step _ proof _ _ =>
    let startTime ← IO.monoNanosNow
    Meta.checkWithKernel proof
    let endTime ← IO.monoNanosNow
    let kernelMs := (endTime - startTime).toFloat / 1000000.0
    IO.println s!"cbv: goal_{n}: {ms} ms, kernel: {kernelMs} ms"

def runCbvTests : MetaM Unit := do
  IO.println "=== Call-By-Value Tactic Tests ==="
  IO.println ""
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  for n in List.range (if bench then 200 else 10) do
    runProblem n

#eval runCbvTests
