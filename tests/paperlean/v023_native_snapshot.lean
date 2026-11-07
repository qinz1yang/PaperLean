import Lean

/- This executable initializes Lean's real runtime before the include-source C++ fixture runs. -/
@[extern "v023_native_snapshot_case"]
opaque snapshotCase (library : @& String) (size : @& String) : IO Unit

def main (args : List String) : IO Unit := do
  match args with
  | [library, size] => snapshotCase library size
  | _ => throw <| IO.userError "expected library and snapshot size (0, 1, word)"
