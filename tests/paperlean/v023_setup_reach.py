# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Instrument the actual selected-row resolver and memoization, without production counters."""
from pathlib import Path
import sys

source = Path(sys.argv[1]).read_text()

def section(start, end):
    a = source.index(start)
    return source[a:source.index(end, a)]

types = section('structure Entry where', 'private initialize headerParser')
state = section('structure State where', 'private initialize standalone')
drain = section('private def State.drain', '-- Write the complete contents')
helpers = section('private def publishBytes', '/-- Encode the fast v1 layout')
algorithm = section('private def commitRow', 'private def indexForCore')
edge = '      let (imp, localImp) := row.imports[next]!'
assert algorithm.count(edge) == 1, 'update resolver edge instrumentation'
algorithm = algorithm.replace('private def resolve (writer', 'private def resolve (visits : IO.Ref Nat) (writer')
algorithm = algorithm.replace(edge, '      visits.modify (· + 1)\n' + edge)

tests = r'''
def nodeName (i : Nat) : Name := .str .anonymous s!"N{i}"
def entry (i : Nat) (children : Array Nat) : Entry := {
  name := nodeName i, owner := `fixture, root := "/fixture", isModule := true
  imports := children.mapIdx fun k c =>
    ({module := nodeName c, importAll := k % 2 == 0, isExported := k % 3 == 0,
      isMeta := k % 5 == 0}, true) }

def graph (edges : Array (Array Nat)) : State :=
  let entries := edges.mapIdx entry
  {entries, byName := entries.foldl (fun m e => m.insert e.name m.size) {}}
def base (s : State) (dir : FilePath) : Base :=
  {file := dir / "base", hash := 42, rows := s.entries, byName := s.byName}
def fresh : IO Writer := return {base := ← IO.mkRef .unplanned, refs := ← IO.mkRef {}}

def check (label : String) (writer : Writer) (dir : FilePath) (b : Base) (s : State)
    (root : Nat) (expected : String) (numVisits : Nat) : IO Unit := do
  let visits ← IO.mkRef 0
  let got ← resolve visits writer dir b s.entries s.byName root
  let result := match got with
    | some (.base hash id) => if hash == b.hash && id == root then "base" else "wrong base"
    | some (.node _) => "node"
    | none => "missing"
  unless result == expected && (← visits.get) == numVisits do
    throw <| IO.userError s!"{label}: {result}, {← visits.get} edge visits; expected {expected}, {numVisits}"

def run (dir : FilePath) : IO Unit := do
  for width in [16, 64, 256, 1024] do
    let s := graph <| #[Array.range width |>.map (· + 1)] ++ Array.replicate width #[]
    let writer ← fresh
    let b := base s dir
    check "star" writer dir b s 0 "base" width
    check "memoized star" writer dir b s 0 "base" 0
  let chain := graph #[#[1], #[2], #[]]
  check "chain" (← fresh) dir (base chain dir) chain 0 "base" 2
  let diamond := graph #[#[1, 2], #[3], #[3], #[]]
  let writer ← fresh
  check "diamond" writer dir (base diamond dir) diamond 0 "base" 4
  check "shared leaf" writer dir (base diamond dir) diamond 3 "base" 0
  let self := graph #[#[0]]
  check "self cycle" (← fresh) dir (base self dir) self 0 "missing" 1
  let cycle := graph #[#[1, 3], #[2], #[1], #[]]
  let writer ← fresh
  check "cycle" writer dir (base cycle dir) cycle 0 "missing" 3
  check "independent child" writer dir (base cycle dir) cycle 3 "base" 0

  let s := graph #[#[1]]
  let b := base s dir
  let writer ← fresh
  check "missing row" writer dir b s 0 "missing" 1
  let s := {s with pending := [fun _ => some (entry 1 #[])]} |>.drain
  check "new row and old root become linked" writer dir b s 0 "node" 1
  check "memoized new closure" writer dir b s 0 "node" 0
  check "new leaf was cached too" writer dir b s 1 "node" 0
  let complete := graph #[#[1], #[]]
  let writer ← fresh
  let b := base complete dir
  check "complete" writer dir b complete 0 "base" 1
  let extra := {complete with pending := [fun _ => some (entry 2 #[])]} |>.drain
  check "completed memo survives drain" writer dir b extra 0 "base" 0
  let e := {entry 0 #[] with imports := #[({module := nodeName 99}, false)]}
  let external : State := {entries := #[e], byName := ({} : Std.HashMap Name Nat).insert e.name 0}
  check "nonlocal absent import" (← fresh) dir (base external dir) external 0 "base" 1
  IO.println "selected closures, retry, and linear edge visits passed"
'''

output = '''import Lake.Config.Module
import Lake.Config.Workspace
import Init.System.Promise
import Init.While
import Std.Data.HashMap.Basic
open System Lean Lake
open Lean.PaperLean.SetupIndex (RecordRef LinkedImport encodeLinked linkedFileName)
namespace ReachRegression
-- All test writes are serial and use a fresh temporary directory.
private def freshGeneration : BaseIO Nat := pure 1
'''
Path(sys.argv[2]).write_text(output + types + state + drain + helpers + algorithm + tests +
    '\nend ReachRegression\ndef main : IO Unit := IO.FS.withTempDir ReachRegression.run\n')
