import Lean.Setup
import Lean.Util.Path

/-!
Tests the JSON encoding of `ModuleSetup.importArts`: artifacts at their default location below a
package root are stored as a root index and part counts, all other entries keep their full paths,
and the older encoding with full paths for every entry is still accepted.
-/

open Lean

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

-- `ModuleSetup` uses the same encoding.
#guard
  let setup : ModuleSetup := { name := `Test, importArts := sample }
  match fromJson? (toJson setup) with
  | .ok (setup' : ModuleSetup) => entries setup'.importArts == entries sample
  | .error _ => false
