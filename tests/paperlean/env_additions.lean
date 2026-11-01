/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
`lean --run env_additions.lean <official lib/lean> <PaperLean lib/lean>` compares what importing each
module of official Lean brings, in the two toolchains, leaving PaperLean's own modules out, and prints
a line for each difference, then `<n> modules compared`:
- the modules that a non-module file gets, and the order in which it gets them (which decides the
  order of the entries of instances, simp theorems and the like);
- the modules that a `module` gets by `public import` and by `import all`, as `importModulesCore`'s
  comment defines them. These are subsets of the first: an edge can leave it alone and change them.
-/

open Lean System

partial def oleans (dir : FilePath) : IO (Array FilePath) := do
  let mut r := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then r := r ++ (← oleans e.path)
    else if e.path.extension == some "olean" then r := r.push e.path
  return r

/-- The imports of each module below `root`. -/
def imports (root : FilePath) : IO (Std.HashMap Name (Array Import)) := do
  let mut g := {}
  for f in ← oleans root do
    let rel := (f.withExtension "").toString.drop (root.toString.length + 1)
    let mod := (rel.toString.splitOn "/").foldl Name.mkStr .anonymous
    g := g.insert mod (← readModuleData f).1.imports
  return g

/-- The modules of PaperLean, which are the additions that the rules allow. -/
def isPaperLean (m : Name) : Bool :=
  (`Lean.PaperLean).isPrefixOf m || (`Lake.PaperLean).isPrefixOf m

/-- The sets of modules that importing a module gets, as bit sets, by module. -/
structure Closures where
  index : Std.HashMap Name Nat
  graph : Std.HashMap Name (Array Import)
  full : Std.HashMap Name Nat := {}
  «public» : Std.HashMap Name Nat := {}
  importAll : Std.HashMap Name Nat := {}

abbrev ClosuresM := StateM Closures

def bit (m : Name) : ClosuresM Nat :=
  return 1 <<< (← get).index[m]!

mutual
  partial def full (m : Name) : ClosuresM Nat := do
    if let some s := (← get).full[m]? then return s
    let mut r := 0
    for i in (← get).graph.getD m #[] do
      r := r ||| (← bit i.module) ||| (← full i.module)
    modify fun c => { c with full := c.full.insert m r }
    return r

  /-- What `A ≥ public` reaches. A `meta` import needs the IR of what the imported module imports. -/
  partial def «public» (m : Name) : ClosuresM Nat := do
    if let some s := (← get).public[m]? then return s
    let mut r := 0
    for i in (← get).graph.getD m #[] do
      if i.isExported then
        r := r ||| (← bit i.module) ||| (← if i.isMeta then full i.module else «public» i.module)
    modify fun c => { c with «public» := c.public.insert m r }
    return r

  /-- What `A ≥ privateAll` reaches. -/
  partial def importAll (m : Name) : ClosuresM Nat := do
    if let some s := (← get).importAll[m]? then return s
    let mut r := 0
    for i in (← get).graph.getD m #[] do
      r := r ||| (← bit i.module) ||| (← if i.isMeta then full i.module else
        if i.importAll then importAll i.module else «public» i.module)
    modify fun c => { c with importAll := c.importAll.insert m r }
    return r
end

/-- The modules that a file importing `m` gets, in the order of `importModulesCore`. -/
partial def order (g : Std.HashMap Name (Array Import)) (m : Name) : Array Name :=
  (go m |>.run ({}, #[])).2.2
where
  go (m : Name) : StateM (NameSet × Array Name) Unit := do
    if (← get).1.contains m then return
    modify fun s => (s.1.insert m, s.2)
    for i in g.getD m #[] do
      go i.module
    modify fun s => (s.1, s.2.push m)

def main (args : List String) : IO UInt32 := do
  let [officialLib, paperleanLib] := args | return 2
  let official ← imports officialLib
  let paperlean ← imports paperleanLib
  let mut index : Std.HashMap Name Nat := {}
  for (m, is) in official.toList ++ paperlean.toList do
    for n in is.map (·.module) |>.push m do
      unless index.contains n do index := index.insert n index.size
  let names := index.toArray
  let ownBits := names.foldl (init := 0) fun s (m, i) => if isPaperLean m then s ||| 1 <<< i else s
  let show' (s : Nat) : List Name := (names.filter fun (_, i) => s.testBit i).toList.map (·.1)
  let compare (m : Name) (kind : String) (a b : Nat) : IO Unit := do
    let b := b ^^^ (b &&& ownBits)
    if a != b then
      IO.println s!"{m}, {kind}: PaperLean adds {show' (b &&& (a ^^^ b))} and lacks {show' (a &&& (a ^^^ b))}"
  let mut co : Closures := { index, graph := official }
  let mut cp : Closures := { index, graph := paperlean }
  let mut compared := 0
  for (m, _) in official do
    unless paperlean.contains m do
      IO.println s!"{m}: not in PaperLean"
      continue
    compared := compared + 1
    for (kind, f) in [("all imports", full), ("public imports", «public»),
        ("through import all", importAll)] do
      let (a, co') := f m |>.run co
      let (b, cp') := f m |>.run cp
      co := co'
      cp := cp'
      compare m kind a b
    let a := order official m
    let b := (order paperlean m).filter (!isPaperLean ·)
    if a != b && a.size == b.size then
      let (x, y) := (a.zip b).toList.find? (fun (x, y) => x != y) |>.getD (default, default)
      IO.println s!"{m}, order: {y} where official Lean has {x}"
  for (m, _) in paperlean do
    unless official.contains m || isPaperLean m do
      IO.println s!"{m}: not in official Lean"
  IO.println s!"{compared} modules compared"
  return 0
