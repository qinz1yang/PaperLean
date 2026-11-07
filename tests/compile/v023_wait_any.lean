-- A waiting pool worker must leave capacity for its queued children.
def main : IO Unit := do
  let work ← IO.mkRef (0 : Nat)
  for _ in [:12] do
    let parent ← BaseIO.asTask do
      let left ← BaseIO.asTask do
        work.modify (· + 1)
        return (41 : Nat)
      let right ← BaseIO.asTask do
        work.modify (· + 1)
        return (42 : Nat)
      IO.waitAny [left, right]
    let result ← IO.wait parent
    unless result == 41 || result == 42 do throw <| IO.userError "wrong queued result"
  -- Already complete tasks keep their input-list tie behavior.
  let first ← IO.waitAny [Task.pure (3 : Nat), Task.pure 4]
  unless first == 3 do throw <| IO.userError "completed-task tie order changed"
  -- An unresolved first task must not hide an already-ready later task.
  let gate ← IO.Promise.new (α := Nat)
  let later ← IO.waitAny [gate.result!, Task.pure 7]
  gate.resolve 5
  unless later == 7 do throw <| IO.userError "waitAny waited for the first task"
  IO.println "waitAny worker progress passed"
