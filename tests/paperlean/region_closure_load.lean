import Lean.CompactedRegion
open Lean

@[extern "lean_region_test_reserve"] opaque reserve (path : @& System.FilePath) : BaseIO Bool
@[extern "lean_region_test_release"] opaque release : BaseIO Unit
@[extern "lean_region_test_mapping"] opaque mapping (path : @& System.FilePath) : BaseIO UInt8
@[extern "lean_region_test_maxrss"] opaque maxrss : BaseIO UInt64

unsafe def main (args : List String) : IO Unit := do
  let [path, count, mode] := args | throw <| IO.userError "expected path, repetitions, mapped|fallback"
  let n := count.toNat!
  unless n > 0 do throw <| IO.userError "count must be positive"
  unless mode == "mapped" || mode == "fallback" do throw <| IO.userError "unknown mode"
  unless (← mapping path) == 0 do throw <| IO.userError "preferred address was not free before test"
  let fallback := mode == "fallback"
  if fallback then
    unless (← reserve path) do throw <| IO.userError "could not reserve preferred address"
  let before ← maxrss
  let mut first := ""
  let expected := "library required for closure relocation is not loaded " ++
    "in this process: '__paperlean_region_cleanup_missing_library__'"
  try
    for i in [:n] do
      let result ← try
        let (_, region) ← CompactedRegion.read (α := Nat → UInt8) path #[]
        region.free
        pure "unexpected success"
      catch ex => pure ex.toString
      unless (result.splitOn expected).length > 1 do
        throw <| IO.userError s!"wrong result: {result}"
      if i == 0 then first := result
      else unless result == first do throw <| IO.userError "error changed across attempts"
      unless (← mapping path) == (if fallback then 1 else 0) do
        throw <| IO.userError "failed read retained a mapping or released the caller's reservation"
    let after ← maxrss
    -- With 64 reads of a 4 MiB fixture, the old fallback leaks about 256 MiB. Allow allocator
    -- high-water noise, while retaining direct mapped-address checks for the mmap case.
    unless after - before < 64 * 1024 * 1024 do
      throw <| IO.userError s!"failed reads grew peak RSS by {after - before} bytes"
    IO.println s!"{n} identical missing-library errors ({mode})"
  finally
    release
  unless (← mapping path) == 0 do throw <| IO.userError "preferred address remains mapped after cleanup"
