import Lean

/-!
Tests the object-graph comparison behind `PAPERLEAN_IMPORT=check` (`lean_paperlean_graph_diff`):
equal graphs match, and differences in contents, sharing, array capacity (only when strict) and
the identity of objects outside the heap are found.
-/

open Lean Lean.PaperLean

def mkList (n : Nat) : IO (List Nat) := pure (List.range n |>.map (· + 1))

unsafe def check (name : String) (expectDiff : Bool) (d : Option String) : IO Unit := do
  if d.isSome != expectDiff then
    throw <| IO.userError s!"{name}: expected {if expectDiff then "a difference" else "no difference"}, got {d}"

unsafe def test : CoreM Unit := do
  let a ← mkList 1000
  let b ← mkList 1000
  check "equal lists" false (graphDiff a b true)
  check "one element differs" true (graphDiff a (a.set 500 0) true)
  -- the same contents with different sharing
  check "sharing" true (graphDiff (a, a) (a, b) true)
  check "same sharing" false (graphDiff (a, a) (b, b) true)
  -- capacity only matters when strict
  let x : Array Nat := (Array.mkEmpty 8).push 1
  let y : Array Nat := (Array.mkEmpty 1).push 1
  check "capacity, strict" true (graphDiff x y true)
  check "capacity, not strict" false (graphDiff x y false)
  check "strings" true (graphDiff "abc" ("ab" ++ (← pure "d")) true)
  check "equal strings" false (graphDiff "abc" ("ab" ++ (← pure "c")) true)
  -- an object of a loaded `.olean` only matches itself, not an equal heap object
  let some ci := (← getEnv).find? ``Nat.succ | throwError "Nat.succ not found"
  check "olean object, itself" false (graphDiff ci.name ci.name true)
  check "olean object vs heap" true (graphDiff ci.name (Name.mkStr (← pure `Nat) "succ") true)
  -- long lists are compared without recursion
  let deep ← mkList 2000000
  let deep' ← mkList 2000000
  check "deep lists" false (graphDiff deep deep' true)

#eval test
