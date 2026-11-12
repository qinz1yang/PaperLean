/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.

Tests that the whitelist's "vetted code" cache (`Lean.PaperLean.Whitelist.isVetted`) is keyed by the
imported code, not only by the declaration's name: two frontends of one process import the same
module name from two search paths, one a copy of the vetted `Type*` (`go 1`) and one a changed copy
(`go 2`, same declaration names).  `noteEntry` for the vetted environment and then for the changed
one must make the recording unusable for the second: its code hash is not the stored one.  On
0.2.3 the changed environment gets the vetted environment's cached answer, so no reason is given.
-/
import Lean
import Lean.PaperLean.Whitelist
import Lean.Elab.Frontend
import Lean.Util.Path

open Lean

/-- The declaration of the `Type*` entry, the one the whitelist stores the hash of. -/
def entryName : Name :=
  `Lean.Elab.Term.«_aux_Mathlib_Tactic_TypeStar___elabRules_Lean_Elab_Term_termType*_1»

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let opts := Options.empty.setBool `internal.cmdlineSnapshots true
  -- the vetted copy (go 1) and the changed copy (go 2), built by the driver script
  initSearchPath (← findSysroot) ["vetted"]
  let some env1 ← Lean.Elab.runFrontend "import Mathlib.Tactic.TypeStar\n" opts "<vetted>" `Vetted
    | throw <| IO.userError "the frontend of the vetted copy failed"
  initSearchPath (← findSysroot) ["changed"]
  enableInitializersExecution
  let some env2 ← Lean.Elab.runFrontend "import Mathlib.Tactic.TypeStar\n" opts "<changed>" `Changed
    | throw <| IO.userError "the frontend of the changed copy failed"
  let some entry := PaperLean.Whitelist.entries.find? (·.decl == entryName)
    | throw <| IO.userError s!"the entry {entryName} is not on the whitelist"
  let h1 := PaperLean.Whitelist.codeHash env1 entryName
  let h2 := PaperLean.Whitelist.codeHash env2 entryName
  IO.println s!"entry {entryName}"
  IO.println s!"stored {entry.hash}"
  IO.println s!"vetted env: module {env1.getModuleIdxFor? entryName}, hash {h1}"
  IO.println s!"changed env: module {env2.getModuleIdxFor? entryName}, hash {h2}"
  -- (the two environments import the same module under the same index, from different code)
  unless env1.getModuleIdxFor? entryName == env2.getModuleIdxFor? entryName do
    throw <| IO.userError "the two environments do not agree on the module index"
  unless h1 == entry.hash do
    throw <| IO.userError s!"the vetted copy does not hash to the stored hash ({h1} vs {entry.hash})"
  -- (the check order: the vetted environment first fills the cache, the changed one must not use it)
  let reasonOf (env : Environment) : IO String := do
    PaperLean.envStartRecording
    -- (the result must be used: an unused pure `noteEntry` is removed by the compiler, and with it
    -- the check)
    let r := PaperLean.Whitelist.noteEntry env entryName false (7 : Nat)
    unless r == 7 do throw <| IO.userError "noteEntry changed its value"
    let (_, _, why) ← PaperLean.envStopRecording
    return why
  let w11 ← reasonOf env1
  let w12 ← reasonOf env2
  let w21 ← reasonOf env1
  let w22 ← reasonOf env2
  IO.println s!"reasons: vetted '{w11}', changed '{w12}', vetted '{w21}', changed '{w22}'"
  -- what the fix must give: an answer is reused only for the environment header it was found for
  let fixedCache ← IO.mkRef ({} : NameMap (EnvironmentHeader × Bool))
  let fixed (env : Environment) : BaseIO Bool := do
    if env.getModuleIdxFor? entryName |>.isNone then return false
    let header := env.header
    if let some (header', r) := (← fixedCache.get).find? entryName then
      let same : Bool := unsafe ptrEq header' header
      if same then return r
    let r := PaperLean.Whitelist.codeHash env entryName == entry.hash
    fixedCache.modify (·.insert entryName (header, r))
    return r
  let m11 ← fixed env1
  let m12 ← fixed env2
  let m21 ← fixed env1
  let m22 ← fixed env2
  IO.println s!"fixed model: vetted {m11}, changed {m12}, vetted {m21}, changed {m22}"
