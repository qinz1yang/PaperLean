import Lean.Setup

/-! Prints the artifact paths of a module setup file, one per line. -/

def main (args : List String) : IO Unit := do
  let setup ← Lean.ModuleSetup.load args[0]!
  for (_, arts) in setup.importArts do
    for part in arts.toArrays do
      for path in part do
        IO.println path
