/-
`PAPERLEAN_IMPORT=check` compares graphs with `Lean.PaperLean.graphDiff`. The linearity bit of
arrays, scalar arrays, and strings is part of their runtime state; a graph that differs only in
that bit must not be reported equal, while an object is equal to itself.
-/
import Lean

open Lean Lean.PaperLean

unsafe def checkDiff {α : Type} (what : String) (a b : α) : IO Unit := do
  for strict in [true, false] do
    if (graphDiff a b strict).isNone then
      throw <| IO.userError s!"graphDiff missed a {what} linearity mark (strict: {strict})"
  if (graphDiff a a true).isSome then
    throw <| IO.userError s!"graphDiff rejected an identical {what}"

unsafe def main : IO Unit := do
  let a : Array Nat := Array.range 3
  let b : Array Nat := (Array.range 3).markLinear
  checkDiff "array" a b
  let x : ByteArray := ByteArray.mk #[1, 2, 3]
  let y : ByteArray := (ByteArray.mk #[1, 2, 3]).markLinear
  checkDiff "scalar-array" x y
  let s : String := "linearity"
  let t : String := s.markLinear
  checkDiff "string" s t
  IO.println "linearity marks are compared"
