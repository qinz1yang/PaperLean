module
public import Lean
import all Lean.PaperLean.TCCache
import all Lean.PaperLean.EnvDeps
open Lean Meta PaperLean.TCCache

private def key (n : Nat) : Key := {
  hash := n.toUInt64, type := ⟨mkNatLit n⟩, decls := #[], mvars := #[], lmvars := #[],
  localInsts := #[], synthPendingDepth := 0, maxResultSize := 0, configKey := 0,
  univApprox := false, cacheInferType := true, opts := {}, isExporting := true }

private def countSame (a b : RetentionCount) : Bool :=
  a.keys == b.keys && a.pending == b.pending && a.entries == b.entries && a.cheap == b.cheap &&
  a.slots == b.slots && a.operations == b.operations

private def valid (s : Entries) : Bool :=
  let a := s.recent.foldl (fun c _ r => c.add r.count) ({} : RetentionCount)
  let b := s.older.foldl (fun c _ r => c.add r.count) ({} : RetentionCount)
  countSame a s.recentCount && countSame b s.olderCount &&
    (retentionUnbounded || (a.keys ≤ retentionKeys && b.keys ≤ retentionKeys &&
      a.slots ≤ retentionSlots && b.slots ≤ retentionSlots))

private unsafe def pendingRecord (k : Key) (ops : Nat) : Stored :=
  let v : NonScalar := unsafeCast (mkConst ``Nat)
  .pending {
    key := k, fvars := #[], result := none,
    raw := ⟨Array.replicate ops (.cache 0 0 v v), Array.replicate ops v, .anonymous, []⟩,
    ngen0 := {}, ngenEnd := 0,
    emptiedTrans := false, emptiedPerm := false, perm := {} }

private unsafe def entryRecord (k : Key) : Stored :=
  let v : NonScalar := unsafeCast (mkConst ``Nat)
  .entry {
    key := k, deps := { accesses := #[], checks := #[] }, result := none,
    names := 0, ops := #[.lookup 0 v none, .insert 0 v v], mayFill := false,
    defEq := {}, namesFree := true }

private unsafe def retentionTests : Bool := Id.run do
  if retentionKeys != 8 || retentionSlots != 256 || !retentionDiagnostics then return false
  let mut s : Entries := {}
  for i in [0:2000] do
    s := s.insert (key i) #[.cheap]
    unless valid s do return false
  if retentionUnbounded then
    unless s.recentCount.keys == 2000 && s.olderCount.keys == 0 do return false
  else
    unless s.recentCount.keys + s.olderCount.keys ≤ 16 && s.evictedKeys > 0 do return false
    let ((_, gone), next) := s.find (key 0)
    s := next
    unless gone.isEmpty do return false
  -- Keep a repeatedly queried older key alive through successive generation rotations.
  s := {}
  s := s.insert (key 0) #[.cheap]
  for i in [1:1000] do
    s := s.insert (key i) #[.cheap]
    let ((_, hot), next) := s.find (key 0)
    s := next
    unless hot.size == 1 && valid s do return false
  unless s.keyHits == 999 && s.ageMax > 0 do return false
  -- Replacement/subtraction and real Pending/Entry record counts, then release oversized payload.
  s := {}
  s := s.insert (key 1) #[pendingRecord (key 1) 4]
  unless s.recentCount.pending == 1 && s.recentCount.operations == 4 && valid s do return false
  s := s.insert (key 1) #[entryRecord (key 1), .cheap]
  unless s.recentCount.pending == 0 && s.recentCount.entries == 1 &&
      s.recentCount.cheap == 1 && s.recentCount.operations == 2 && valid s do return false
  s := s.insert (key 1) #[pendingRecord (key 1) 1000]
  let ((_, got), next) := s.find (key 1)
  s := next
  if retentionUnbounded then
    unless got.size == 1 do return false
  else
    unless got.isEmpty && s.oversized == 1 && s.recentCount.keys == 0 do return false
  s := s.insert (key 1) #[]
  unless valid s && s.recentCount.keys == 0 && s.olderCount.keys == 0 do return false
  return true

run_meta do
  unless unsafe retentionTests do throwError "retention invariant failed"
