/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Setup
import Lean.Util.Path

/-!
Tests the compact JSON encoding of `ModuleSetup.importArts`: artifacts at their default location
below a package root are stored as a root index and part counts, all other entries keep their full
paths, and official Lean's encoding with full paths for every entry is accepted too. Tests the setup
index of `paperlean build`: the records read back as written, the artifacts computed from them are
those that `Lake.fetchTransImportArts` gives, and a damaged index gives an error.
-/

open Lean

-- (the encoding's functions have no instances outside this test)
local instance : ToJson (NameMap ImportArtifacts) := ⟨PaperLean.artifactsToJson⟩
local instance : FromJson (NameMap ImportArtifacts) := ⟨PaperLean.artifactsFromJson?⟩

def mkArts (root : System.FilePath) (mod : Name) (oleanExts irExts : Array String) : ImportArtifacts :=
  .ofArrays #[oleanExts.map (modToFilePath root mod ·), irExts.map (modToFilePath root mod ·)]

def entries (m : NameMap ImportArtifacts) : List (Name × Array (Array System.FilePath)) :=
  m.foldl (fun acc k v => (k, v.toArrays) :: acc) [] |>.reverse

def roundTrips (m : NameMap ImportArtifacts) : Bool :=
  match fromJson? (toJson m) with
  | .ok m' => entries m' == entries m
  | .error _ => false

def mathlib : System.FilePath := "/w/.lake/packages/mathlib/.lake/build/lib/lean"
def localRoot : System.FilePath := "/w/.lake/build/lib/lean"

def sample : NameMap ImportArtifacts :=
  ({} : NameMap ImportArtifacts)
  |>.insert `Mathlib.Algebra.Group.Basic
    (mkArts mathlib `Mathlib.Algebra.Group.Basic #["olean", "olean.server", "olean.private"] #["ir.sig", "ir"])
  |>.insert `Mathlib.Order.Basic
    (mkArts mathlib `Mathlib.Order.Basic #["olean", "olean.server"] #["ir.sig", "ir"])
  |>.insert `Lib.Foo (.ofArrays #[#[modToFilePath localRoot `Lib.Foo "olean"]])
  |>.insert `Lib.«Foo.Bar» (mkArts localRoot `Lib.«Foo.Bar» #["olean"] #[])
  -- not at the default location (e.g. restored from an artifact cache)
  |>.insert `Cached (.ofArrays #[#["/cache/0123.olean", "/cache/4567.olean.server"], #[]])
  -- not a prefix of the usual parts
  |>.insert `Odd (.ofArrays #[#[modToFilePath localRoot `Odd "olean", modToFilePath localRoot `Odd "olean.private"]])
  |>.insert `Empty (.ofArrays #[])

#guard roundTrips sample
#guard roundTrips {}

def small : NameMap ImportArtifacts :=
  ({} : NameMap ImportArtifacts)
  |>.insert `A.B (mkArts "/w/lib" `A.B #["olean", "olean.server", "olean.private"] #["ir.sig", "ir"])
  |>.insert `C (.ofArrays #[#["/cache/1.olean"], #[]])
  |>.insert `D (mkArts "/w/lib" `D #["olean"] #[])

/-- info: {"":["/w/lib"],"A.B":[0,3,2],"C":[["/cache/1.olean"],[]],"D":[0,1,0]} -/
#guard_msgs in
#eval IO.println (toJson small).compress

/-- info: {} -/
#guard_msgs in
#eval IO.println (toJson ({} : NameMap ImportArtifacts)).compress

-- The older encoding, with full paths for every entry, is still accepted.
def oldEncoding : Except String (NameMap ImportArtifacts) :=
  Json.parse r#"{"A.B": [["/w/lib/A/B.olean"], []], "C": [["/c/C.olean"]]}"# >>= fromJson?

#guard match oldEncoding with
  | .ok m => (entries m).length == 2 &&
    (m.find? `A.B).map (·.toArrays) == some #[#[("/w/lib/A/B.olean" : System.FilePath)], #[]] &&
    (m.find? `C).map (·.toArrays) == some #[#[("/c/C.olean" : System.FilePath)]]
  | .error _ => false

-- Malformed compact entries are rejected.
#guard (Json.parse r#"{"": ["/w/lib"], "A": [1, 1, 0]}"# >>=
    fromJson? : Except String (NameMap ImportArtifacts)) matches .error _
#guard (Json.parse r#"{"": ["/w/lib"], "A": [0, 4]}"# >>=
    fromJson? : Except String (NameMap ImportArtifacts)) matches .error _

def big : NameMap ImportArtifacts := (List.range 1000).foldl (init := {}) fun m i =>
  let mod := Name.mkStr2 "Mathlib" s!"Module{i}"
  m.insert mod (mkArts mathlib mod #["olean", "olean.server", "olean.private"] #["ir.sig", "ir"])

def fullPathsSize (m : NameMap ImportArtifacts) : Nat :=
  (Json.obj <| m.foldl (fun n k v => n.insert k.toString (toJson v.toArrays)) ∅).compress.length

#guard roundTrips big
#guard (toJson big).compress.length * 8 < fullPathsSize big

-- `PaperLean.setupToJsonCompact` uses the same encoding; `toJson` of a `ModuleSetup` gives official
-- Lean's, with full paths; `PaperLean.setupFromJsonCompact?`, which `ModuleSetup.load` uses, reads both.
def readsBack (j : Json) : Bool :=
  match PaperLean.setupFromJsonCompact? j with
  | .ok setup' => entries setup'.importArts == entries sample
  | .error _ => false

def hasRoots (j : Json) : Bool :=
  ((j.getObjValD "importArts").getObjVal? "").toOption.isSome

#guard
  let setup : ModuleSetup := { name := `Test, importArts := sample }
  readsBack (toJson setup) && !hasRoots (toJson setup) &&
    readsBack (PaperLean.setupToJsonCompact setup) && hasRoots (PaperLean.setupToJsonCompact setup)

/-! The setup index of `paperlean build` (`PaperLean.SetupIndex`). -/

open PaperLean.SetupIndex

def edge (target : Nat) (importAll : Bool := false) (isExported : Bool := false)
    (isMeta : Bool := false) : Edge :=
  { target, importAll, isExported, isMeta }

def mods : Array Name :=
  #[`R, `A, `B, `C, `D, `E, `F, `G, `H, `I, `J, `K, `L, `M, `N, `R2, `P, `Lib.«Foo.Bar», `S]

def ix (n : Name) : Nat := (mods.findIdx? (· == n)).getD 0

/-- `R` and `R2` import the others in all the ways that `Lake.fetchTransImportArts` tells apart. -/
def records : Array Record := mods.map fun n =>
  let imports := match n with
    | `R => #[edge (ix `A) (isExported := true), edge (ix `B) (importAll := true),
        edge (ix `C) (isMeta := true), edge (ix `D), edge noModule (isExported := true)]
    | `A => #[edge (ix `E) (isExported := true), edge (ix `F)]
    | `B => #[edge (ix `G) (importAll := true), edge (ix `H) (isExported := true), edge (ix `J),
        edge (ix `P) (isExported := true)]
    | `C => #[edge (ix `I)]
    | `D => #[edge (ix `K) (isExported := true), edge (ix `L)]
    | `G => #[edge (ix `M), edge (ix `P) (importAll := true)]
    | `R2 => #[edge (ix `N), edge (ix `D), edge (ix `Lib.«Foo.Bar»)]
    | `N => #[edge (ix `F)]
    | `S => #[edge unknown (isExported := true)]
    | _ => #[]
  { name := n, root := if n == `Lib.«Foo.Bar» then 1 else 0,
    isModule := !(n == `R2 || n == `N || n == `Lib.«Foo.Bar»), imports }

def bytes : ByteArray := encode #[localRoot.toString, mathlib.toString] records
def index? : Except String Index := Index.read ("/some/dir" / fileName bytes) bytes

def strings (m : NameMap ImportArtifacts) : List (Name × Array (Array String)) :=
  (entries m).map fun (n, a) => (n, a.map (·.map toString))

def artsOf (root : Name) : Except String (List (Name × Array (Array String))) := do
  return strings (← (← index?).importArts root (ix root))

def expected (all : List Name) (mods : List Name) : List (Name × Array (Array String)) :=
  strings <| mods.foldl (init := {}) fun m n =>
    let root := if n == `Lib.«Foo.Bar» then mathlib else localRoot
    let isModule := !(n == `N || n == `Lib.«Foo.Bar»)
    m.insert n (artifactsAt root n isModule (all.contains n))

#guard match index? with
  | .ok i => (List.range mods.size).all fun j => match i.record j with
    | .ok r => r.name == records[j]!.name && r.root == records[j]!.root &&
        r.isModule == records[j]!.isModule &&
        r.imports.map (fun e => (e.target, e.importAll, e.isExported, e.isMeta)) ==
          records[j]!.imports.map (fun e => (e.target, e.importAll, e.isExported, e.isMeta))
    | .error _ => false
  | .error _ => false

-- A `module`: `import all` adds `.olean.private` along `import all` chains, widening `P`; `meta`
-- imports reach `I`, private imports of imported modules (`F`, `L`) are left out.
#guard (artsOf `R).toOption ==
  some (expected [`B, `G, `P] [`A, `B, `C, `D, `E, `G, `H, `I, `J, `K, `M, `P])
-- No `module`: everything, with `.olean.private`.
#guard (artsOf `R2).toOption ==
  some (expected [`D, `F, `K, `L, `N, `Lib.«Foo.Bar»] [`D, `F, `K, `L, `N, `Lib.«Foo.Bar»])
#guard (artifactsAt mathlib `Lib.«Foo.Bar» false true).toArrays ==
  #[#[mathlib / "Lib" / "Foo.Bar.olean"]]

-- What it cannot give is an error.
#guard artsOf `S matches .error _
#guard (do (← index?).importArts `A (ix `R)) matches .error _
#guard (do (← index?).importArts `R mods.size) matches .error _
#guard Index.read "/some/dir/setup-0.paperlean" bytes matches .error _
def truncated : ByteArray := bytes.extract 0 (bytes.size * 6 / 10)
#guard (do (← Index.read (fileName truncated) truncated).importArts `R (ix `R)) matches .error _
