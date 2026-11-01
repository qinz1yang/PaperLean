/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Init
public import Std.Data.HashSet.Basic

/-!
The summary at the end of `paperlean build` of what was not accelerated, why and where, from what the
`lean` processes of the build wrote (`PAPERLEAN_REUSE_STATS`, `Lean.PaperLean.SectionVars.writeReuseStats`):
lines of the file, the reuses, the searches and the elaborations done in full, and the reasons
(`Lean.PaperLean.Speculation.Reasons.render`); and what each import did with the native code of the
modules of dependencies (`PAPERLEAN_NATIVE_STATS`, `src/paperlean/native_libs.cpp`).
-/

namespace Lake.PaperLean.ReuseSummary

/-- How many of the reasons and of their locations a summary shows. -/
def maxReasons := 10
def maxLocations := 3

private structure Reason where
  text : String
  total : Nat := 0
  /-- The count in a module, with the file and the position of its first. -/
  places : Array (Nat × String) := #[]

private def addReason (rs : Array Reason) (text : String) (n : Nat) (place : String) : Array Reason :=
  match rs.findIdx? (·.text == text) with
  | some i => rs.modify i fun r => { r with total := r.total + n, places := r.places.push (n, place) }
  | none => rs.push { text, total := n, places := #[(n, place)] }

/-- The reasons of the field `field` of a line, of the module `file`, added to `rs`, for the kind of
reuse `kind`, and the number of computations that it says were left out of reuse altogether. What a
reuse does not refuse is no reason here. -/
private def addField (rs : Array Reason) (kind file field : String) : Array Reason × Nat := Id.run do
  let mut rs := rs
  let mut excluded := 0
  for part in field.splitOn " | " do
    -- (`why=count@position`, and `why` may hold `=` and `@`)
    let some (rest, pos) := splitLast part "@" | continue
    let some (why, count) := splitLast rest "=" | continue
    let some n := count.toNat? | continue
    if why.startsWith "not eligible: " then
      excluded := excluded + n
    let some why := (why.dropPrefix? "not kept: ").map (·.toString) <|>
      (why.dropPrefix? "not reused: ").map (·.toString) <|>
      (why.dropPrefix? "not eligible: ").map (·.toString) | continue
    for one in reasonsOf why do
      rs := addReason rs s!"{kind}: {one}" n s!"{file}:{pos}"
  return (rs, excluded)
where
  /-- The reasons of a recording that is not usable each on its own, e.g. each elaborator that it ran
  (`envStopRecording`). -/
  reasonsOf (why : String) : List String :=
    let recordable := "not recordable: "
    match why.dropPrefix? recordable with
    | some rest => (rest.toString.splitOn "; ").map (recordable ++ ·)
    | none => [why]
  splitLast (s sep : String) : Option (String × String) :=
    match s.splitOn sep with
    | [] | [_] => none
    | parts => some (sep.intercalate parts.dropLast, parts.getLast!)

/-- What the imports of a build did with the native code of the modules of dependencies, each as its
`lean` told it. A module can fare differently in two imports, so what one says takes nothing from what
another says, and only modules that an import had are here. -/
public structure Fallbacks where
  /-- The modules that ran in the interpreter in an import, with the reason of the first that told of
  it. That is `imports` for a module that imports one that did, and `rejected` or `left out` for one
  that a library rejects or none has, of files that `paperlean prepare` read. -/
  modules : Array (String × String) := #[]
  /-- Those of them for which that holds of each import of them that no plugin loads them for. -/
  always : Std.HashSet String := {}
  /-- The modules whose code a plugin loaded in an import, as by the target's own `precompileImports`. -/
  loaded : Std.HashSet String := {}
  /-- Whether a `lean` told only part of this: there may be modules of each kind that it did not name. -/
  more : Bool := false

/-- What the lines of the statistics `text` of a build say (`src/paperlean/native_libs.cpp`):
`native\t<module>\t<scope>\t<why>` of a module that ran in the interpreter, `scope` being `always` or
`here`, `native\t<module>\tloaded`, and `native\t*\tmore`. -/
public def fallbacks (text : String) : Fallbacks := Id.run do
  let mut out : Fallbacks := {}
  let mut seen : Std.HashSet String := {}
  for line in text.splitOn "\n" do
    match line.splitOn "\t" with
    | ["native", "*", "more"] => out := { out with more := true }
    | ["native", m, "loaded"] => out := { out with loaded := out.loaded.insert m }
    | ["native", m, scope, why] =>
      if scope == "always" then
        out := { out with always := out.always.insert m }
      unless seen.contains m do
        seen := seen.insert m
        out := { out with modules := out.modules.push (m, why) }
    | _ => pure ()
  return out

/-- The lines of the summary of `f`. What an import said of a module stands, as it looked at the
module's files as they are. Only for files that prepared data knows does what it holds of them apply, and
say more: `prepared` is its reason for a module, and `imports` whether the module imports one that runs
in the interpreter, which hold no more of what changed (`keptFindings`, `currentFindings`). A module
is said to run there without more only if nothing says
otherwise of any import of the build, which takes all that the imports did. -/
public def fallbackLines (f : Fallbacks) (prepared : String → Option String) (imports : String → Bool) :
    Array String :=
  let (all, some') := f.modules.partition fun (m, _) =>
    !f.more && f.always.contains m && !f.loaded.contains m
  let atLeast := if f.more then "at least " else ""
  list all s!"{all.size} dependency module(s) run in the interpreter, with the same results but slower:" ++
    list some' s!"{atLeast}{some'.size} dependency module(s) run in the interpreter in some imports:"
where
  list (ms : Array (String × String)) (heading : String) : Array String := Id.run do
    if ms.isEmpty then return #[]
    let (importers, own) := ms.partition fun (m, why) =>
      why == "imports" || ((why == "rejected" || why == "left out") && imports m)
    let mut out := #[s!"paperlean: {heading}"]
    for (m, why) in own.take maxReasons do
      let reason := match why with
        | "rejected" => (prepared m).getD "its library does not use it"
        | "left out" => (prepared m).getD "no prepared native library has it"
        | _ => why
      out := out.push s!"  {m}: {reason}"
    if own.size > maxReasons then
      out := out.push s!"  and {own.size - maxReasons} more"
    unless importers.isEmpty do
      out := out.push s!"  {if own.isEmpty then "" else "and "}{importers.size} that import one that does"
    if f.more then
      out := out.push "  and perhaps others: `lean` names the first 100 of an import"
    return out

/-- The lines of the summary of the statistics `text` of a build in the directory `root`; none if no
module was compiled. -/
public def lines (text root : String) : Array String := Id.run do
  let mut modules := 0
  let mut tr := 0
  let mut ts := 0
  let mut sr := 0
  let mut ss := 0
  let mut rs : Array Reason := #[]
  for line in text.splitOn "\n" do
    let [file, r, n, _, tcWhy, sr', sn, _, svWhy] := line.splitOn "\t" | continue
    let file := (file.dropPrefix? (root ++ "/")).map (·.toString) |>.getD file
    modules := modules + 1
    tr := tr + r.toNat?.getD 0
    ts := ts + n.toNat?.getD 0
    sr := sr + sr'.toNat?.getD 0
    ss := ss + sn.toNat?.getD 0
    let (rs', tx) := addField rs "typeclass results" file tcWhy
    let (rs'', sx) := addField rs' "section variables" file svWhy
    rs := rs''
    ts := ts + tx
    ss := ss + sx
  if modules == 0 then
    return #[]
  let mut out := #[s!"paperlean: compiled {modules} module(s): reused {tr} typeclass results and the \
    section variables of {sr} commands; {ts} searches and {ss} elaborations of section variables \
    ran in full."]
  unless rs.isEmpty do
    out := out.push "paperlean: not reused, by reason, with the modules that have the most:"
  -- (each list shows its largest: an elaborator that is rare in a large build is still named)
  let sorted := rs.qsort (·.total > ·.total)
  let (elaborators, others) := sorted.partition (·.text.contains "the elaborator ")
  for group in [elaborators, others] do
    for r in group.take maxReasons do
      let places := (r.places.qsort (·.1 > ·.1)).take maxLocations |>.map (·.2)
      out := out.push s!"  {r.total} {r.text} ({", ".intercalate places.toList})"
    if group.size > maxReasons then
      out := out.push s!"  and {group.size - maxReasons} more reason(s)"
  return out

end Lake.PaperLean.ReuseSummary
