import Std.Internal.UV.Loop

def main : IO Unit := do
  Std.Internal.UV.Loop.configure {}
  Std.Internal.UV.Loop.configureChecked {}
  Std.Internal.UV.Loop.configureChecked { accumulateIdleTime := true }
  discard Std.Internal.UV.Loop.alive
