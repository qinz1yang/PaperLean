import Lean.CompactedRegion
open Lean

-- First verify a successful round trip within this executable. The cleanup test then changes
-- only the saved library identity to force a missing-library error on every platform. Pass the
-- byte count at run time to retain a substantial captured payload in the closure's saved graph.
@[noinline] def makeClosure (bytes : ByteArray) : Nat → UInt8 :=
  fun i => bytes[i % bytes.size]!

unsafe def main (args : List String) : IO Unit := do
  let [path, count] := args | throw <| IO.userError "expected output path and byte count"
  let n := count.toNat!
  unless n > 0 do throw <| IO.userError "count must be positive"
  let f := makeClosure (ByteArray.mk (Array.replicate n 37))
  let _ ← CompactedRegion.save path `RegionCleanup f #[] none true
  -- The same executable can load and free the successful region without invalidating f.
  let (g, region) ← CompactedRegion.read (α := Nat → UInt8) path #[]
  unless g 13 == 37 do throw <| IO.userError "round-trip value differs"
  region.free
  unless f 29 == 37 do throw <| IO.userError "source closure changed"
