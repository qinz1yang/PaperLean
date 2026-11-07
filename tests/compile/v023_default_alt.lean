module
import all Lean.Compiler.LCNF.Simp.DefaultAlt
import Lean.Compiler.LCNF.AlphaEqv

open Lean Compiler LCNF

def body (tag serial : Nat) : Code .pure :=
  let x : FVarId := ⟨.num `local serial⟩
  .let { fvarId := x, binderName := .num `value serial,
         type := mkConst ``Nat, value := .lit (.nat tag) } (.return x)

def alternatives (tags : Array Nat) : Array (Alt .pure) :=
  tags.zipIdx.map fun (tag, i) => .alt (.num `Constructor i) #[] (body tag i)

def reference (alts : Array (Alt .pure)) : Nat × Nat := Id.run do
  let mut best := 0
  let mut maximum := 0
  for i in [:alts.size] do
    let mut count := 1
    for j in (i + 1)...alts.size do
      if Code.alphaEqv alts[j]!.getCode alts[i]!.getCode then count := count + 1
    if count > maximum then
      best := i
      maximum := count
  return (best, maximum)

def words : Nat → List (Array Nat)
  | 0 => [#[]]
  | n+1 => (words n).flatMap fun xs => [xs.push 0, xs.push 1, xs.push 2]

public def main : IO Unit := do
  unless Code.alphaEqv (body 7 1) (body 7 99) do
    throw <| IO.userError "fixture did not exercise alpha-renamed bindings"
  for n in [1, 2, 3, 4, 5, 6, 7] do
    for tags in words n do
      let alts := alternatives tags
      let (index, count) := reference alts
      let (actual, occurrences) := Lean.Compiler.LCNF.Simp.getMaxOccs alts
      let .alt constructor _ _ := actual | throw <| IO.userError "unexpected default fixture arm"
      unless constructor == .num `Constructor index && occurrences == count do
        throw <| IO.userError s!"production first winner changed: {tags}"
  IO.println "production default-arm winner passed"
