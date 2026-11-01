/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
import Init
public import Lake.Load.Config
public import Lake.Config.Workspace
import Lake.Load.Workspace
import Lake.Config.LeanExe
import Lake.PaperLean.Env
import Lake.PaperLean.Prepare
import Lake.PaperLean.Update
import Lake.PaperLean.BuildData
import Lake.PaperLean.ReuseSummary
import Lean.PaperLean.System
import Lean.PaperLean.OLeanPack

/-!
The `paperlean` command (`lake paperlean`, run by the toolchain's `bin/paperlean`, which the front end
in elan's `bin` runs for the Lean version of a project: `frontEnd`). A project keeps official Lean as
its toolchain, which `lake build` and the editor use; `paperlean build` and the other commands run
this toolchain's Lake with prepared data and packing (`runLake`), `paperlean build` in this process
where it can (`runBuild`).
-/

open System Lean

namespace Lake.PaperLean

def usage : String := "usage: paperlean <command> [arguments]

commands:
  prepare [--all] [-j N] [--no-native] [names]
                            prepare packs, the import image and native libraries of the dependencies:
                            of all of them, or of the named packages (or packages of the named
                            libraries) with the packages they depend on that are not prepared yet,
                            keeping the others' data; with --all, or if it is named, also a pack of
                            the root package
  build [--rebuild-deps] [--prepare[=names]] [lake arguments]
                            check the dependencies, report whether prepared data is used, then run
                            `lake build`; with --prepare, pack the root package's modules that
                            changed afterwards (named dependencies are prepared again in full)
  cache get [arguments]     download built dependencies, then prepare them
  update [names]            update the dependencies if a PaperLean for the Lean version they then
                            need is available, then prepare them; nothing changes otherwise
  status [--verify]         show the prepared data and whether Lean uses it; with --verify, also
                            read the packs and the import image whole to check that they are as
                            written
  clean [names]             delete prepared data: all of it, or that of the named packages and of
                            the prepared packages that depend on them
  install                   install or update the `paperlean` front end in elan's `bin`
  --version                 print PaperLean's version and the Lean release it is built on; outside
                            a project, the installed PaperLean toolchains"

/-- The edit distance of `a` and `b`. -/
def editDistance (a b : String) : Nat := Id.run do
  let a := a.toList.toArray; let b := b.toList.toArray
  let mut prev := (List.range (b.size + 1)).toArray
  for h : i in [0:a.size] do
    let mut cur := #[i + 1]
    for h' : j in [0:b.size] do
      let c := if a[i] == b[j] then prev[j]! else prev[j]! + 1
      cur := cur.push (min c (min (prev[j + 1]! + 1) (cur[j]! + 1)))
    prev := cur
  return prev[b.size]!

/-- The package of `ws` named `name`, or the package of its library named `name`: an exact match,
else a case-insensitive one; otherwise why not. -/
def findPackage (ws : Workspace) (name : String) : Except String Package := do
  let pkgs := ws.packages
  -- every package and library by name, with what to call it in a message
  let cands : Array (String × String × Package) := pkgs.flatMap fun pkg =>
    #[(pkg.prettyName, s!"package {pkg.prettyName}", pkg)] ++
      pkg.leanLibs.map fun lib =>
        let n := lib.name.toString (escape := false)
        (n, s!"library {n} of {pkg.prettyName}", pkg)
  let pick (ms : Array (String × String × Package)) : Option (Except String Package) :=
    let ps := ms.foldl (init := #[]) fun (ps : Array Package) (_, _, p) =>
      if ps.any (·.baseName == p.baseName) then ps else ps.push p
    if h : ps.size = 1 then some (.ok ps[0])
    else if ps.size > 1 then
      some (.error s!"'{name}' matches several packages: {", ".intercalate (ms.map (·.2.1)).toList}")
    else none
  if let some r := pick (cands.filter (·.1 == name)) then return ← r
  if let some r := pick (cands.filter (·.1.toLower == name.toLower)) then return ← r
  let all := ", ".intercalate (pkgs.map (·.prettyName)).toList
  let closest := cands.foldl (init := none) fun best? (n, descr, _) =>
    let d := editDistance n.toLower name.toLower
    match best? with
    | some (_, bd) => if d < bd then some (descr, d) else best?
    | none => some (descr, d)
  match closest with
  | some (descr, d) =>
    if d ≤ max 2 (name.length / 3) then
      throw s!"there is no package or library '{name}'; did you mean the {descr}? The packages are: {all}"
    else throw s!"there is no package or library '{name}'. The packages are: {all}"
  | none => throw s!"there is no package or library '{name}'"

/-- How the variables of prepared data are set, and whether prepared data is used. -/
def dataUse (ws : Workspace) : IO String := do
  if ← explicitDataVars then
    let set ← dataVars.filterM fun v => return (← IO.getEnv v).isSome
    return s!"not used: {", ".intercalate set.toList} set explicitly (explicit variables win; \
      unset them to use the prepared data)"
  match ← readPreparedData ws.dir with
  | none => return "none prepared: run `paperlean prepare`"
  | some (.error e) => return s!"not used: {e}; run `paperlean prepare`"
  | some (.ok d) =>
    match d.mismatch? with
    | some why => return s!"not used: {why}; run `paperlean prepare`"
    | none =>
      if d.isEmpty then return "none prepared: run `paperlean prepare`"
      for p in d.packs do
        let why ← Lean.PaperLean.OLeanPack.whyIgnored (dataDir ws.dir / p).toString
        unless why.isEmpty do return s!"not used: {p}: {why}; run `paperlean prepare`"
      let parts := toString d.packs.size ++ " pack(s)" ++ (if d.image?.isSome then ", an import image" else "") ++
        (if d.native.isEmpty then "" else s!", {d.native.size} native libraries")
      return s!"used: {parts}"

/-- The Lean release PaperLean is built on: the part of its version after `-lean`. -/
def upstreamVersion : String :=
  match Lean.PaperLean.version.splitOn "-lean" with
  | [_, v] => v
  | _ => Lean.versionString

/-- The Lean version that a `lean-toolchain` names, e.g. `4.35.0-rc3` for `leanprover/lean4:v4.35.0-rc3`. -/
def toolchainVersion (tc : String) : String :=
  let tc := (tc.dropEndWhile Char.isWhitespace).toString
  let v := match tc.splitOn ":" with | [_, v] => v | _ => tc
  if v.startsWith "v" then (v.drop 1).toString else v

/-- The build githash in the header of the `.olean` file `f` (`library/module.cpp`, `olean_header`). -/
def oleanGithash? (f : FilePath) : IO (Option String) := do
  let bytes ← (← IO.FS.Handle.mk f .read).read 80
  if bytes.size < 80 then return none
  return (String.fromUTF8? (bytes.extract 40 80)).map fun s => (s.takeWhile (· != '\x00')).toString

/-- An `.olean` file below `dir`, from the files of a directory before its subdirectories. -/
partial def oleanBelow? (dir : FilePath) : IO (Option FilePath) := do
  let entries ← dir.readDir
  if let some e := entries.find? (·.fileName.endsWith ".olean") then
    return some e.path
  for e in entries do
    if ← e.path.isDir then
      if let some f ← oleanBelow? e.path then return some f
  return none

/-- An `.olean` file of `pkg`: that of a root module of one of its libraries, else any. -/
def someOLean? (pkg : Package) : IO (Option FilePath) := do
  for lib in pkg.leanLibs do
    for root in lib.roots do
      let f := Lean.modToFilePath pkg.leanLibDir root "olean"
      if ← f.pathExists then return some f
  if ← pkg.leanLibDir.isDir then oleanBelow? pkg.leanLibDir else return none

/-- Why the dependencies do not match this PaperLean, if they do not: a dependency whose `.olean`
files another Lean built, or that is not built and asks for another Lean release; and notes on those
that ask for another Lean release but that this Lean built (which decides whether the build rebuilds
them). -/
def dependencyMismatches (ws : Workspace) : IO (Array String × Array String) := do
  let mut out := #[]
  let mut notes := #[]
  for pkg in dependencies ws do
    let tcFile := pkg.dir / "lean-toolchain"
    let mut asks := #[]
    if ← tcFile.pathExists then
      let v := toolchainVersion (← IO.FS.readFile tcFile)
      if v != upstreamVersion then
        asks := #[s!"{pkg.prettyName} asks for Lean {v} (its lean-toolchain)"]
    let gh? ← match ← someOLean? pkg with
      | some f => oleanGithash? f
      | none => pure none
    match gh? with
    | some gh =>
      if gh != Lean.githash then
        out := out ++ asks |>.push s!"{pkg.prettyName} was built by another Lean (githash {gh.take 12})"
      else
        notes := notes ++ asks.map (· ++ ", but this Lean built it")
    | none => out := out ++ asks
  return (out, notes)

/-- How many packed modules of the used prepared data changed since packing, if any did. -/
def staleNote (ws : Workspace) : IO String := do
  let some (.ok d) ← readPreparedData ws.dir | return ""
  if d.mismatch?.isSome || (← explicitDataVars) then return ""
  let mut stale := 0
  let mut total := 0
  for p in d.packs do
    if p.endsWith "/deps.paperlean" then
      if let .ok (s, t) ← (Lean.PaperLean.OLeanPack.staleness (dataDir ws.dir / p).toString).toBaseIO then
        stale := stale + s; total := total + t
  if let (some base, delta?) := rootPacks d then
    let packs := (delta?.toArray.push base).map fun (p : String) => dataDir ws.dir / p
    if let .ok (s, t) ← (packStaleness ws.root packs).toBaseIO then
      stale := stale + s; total := total + t
  if stale == 0 then return ""
  return s!"; {stale} of {total} packed modules changed since packing and are read from disk \
    (run `paperlean prepare`)"

/-- `l` as `paperlean status` tells of it, where no import has looked at its modules: `currentFindings`,
only for modules that still exist, and with what was found only of the files of the pack in use. -/
def statusFindings (ws : Workspace) (d : PreparedData) (l : PreparedNative) : IO PreparedNative := do
  let l ← match ws.packages.find? (pkgKey · == l.pkg), d.packs.find? (·.endsWith "/deps.paperlean") with
    | some pkg, some pack => keptFindings pkg (dataDir ws.dir / pack) l
    | _, _ => pure l
  let l := currentFindings ws l
  let exist (m : String) : IO Bool := match ws.findModule? m.toName with
    | some mod => mod.leanFile.pathExists
    | none => pure false
  return { l with
    interpreted := ← l.interpreted.filterM (exist ·.1)
    importers := ← l.importers.filterM exist
    plugin := ← l.plugin.filterM (exist ·.1)
    others := ← l.others.filterM exist
    outdated := ← l.outdated.filterM exist }

def status (ws : Workspace) (verify := false) : IO UInt32 := do
  IO.println s!"PaperLean {Lean.PaperLean.version}, build {Lean.PaperLean.build} \
    (Lean {Lean.versionString}, {Lean.githash})"
  IO.println s!"workspace: {ws.dir}"
  IO.println s!"prepared data ({dataDir ws.dir}): {← dataUse ws}"
  if let some (.ok d) ← readPreparedData ws.dir then
    let prepared := if d.mismatch?.isNone then d.packages else #[]
    for pkg in dependencies ws do
      IO.println s!"  package {pkg.prettyName}: \
        {if prepared.contains (pkgKey pkg) then "prepared" else "not prepared"}"
    for line in ← currentSummary ws d.libs d.summary do
      IO.println s!"  native library of {line}"
    for l in ← d.libs.mapM (statusFindings ws d) do
      for (m, why) in l.interpreted do
        IO.println s!"    {m} runs in the interpreter where no plugin loads it: {why}"
      for m in l.importers do
        IO.println s!"    {m} runs in the interpreter where no plugin loads it: it imports one that does"
      for (m, why) in l.plugin do
        IO.println s!"    {m} loads as a plugin, not from the prepared library: {why}"
      for m in l.others do
        IO.println s!"    {m} is in no default library of its package, so it runs in the interpreter \
          where no plugin loads it"
      for m in l.outdated do
        IO.println s!"    {m} runs in the interpreter where no plugin loads it: what `paperlean prepare` \
          found of it may no longer hold"
    for f in d.packs ++ d.image?.toArray ++ d.native do
      let file := dataDir ws.dir / f
      -- (another command may delete it meanwhile)
      if let .ok md ← file.metadata.toBaseIO then
        let stale ← if f.endsWith "/deps.paperlean" then
            match ← (Lean.PaperLean.OLeanPack.staleness file.toString).toBaseIO with
            | .ok (s, t) => pure s!", {s} of {t} modules changed since packing"
            | .error e => pure s!", {e}"
          else if f.endsWith "/root.paperlean" then
            -- with the pack of its changes
            let packs := ((rootPacks d).2.toArray.map fun (p : String) => dataDir ws.dir / p).push file
            match ← (packStaleness ws.root packs).toBaseIO with
            | .ok (s, t) => pure s!", {s} of {t} modules changed since packing"
            | .error e => pure s!", {e}"
          else if f.endsWith ".delta.paperlean" then
            pure s!", the modules of {ws.root.prettyName} that changed since its pack was written"
          else pure ""
        let verified ← if verify && d.packs.contains f then
            match ← Lean.PaperLean.OLeanPack.verify file.toString with
            | "" => pure ", verified"
            | why => pure s!", not usable: {why}"
          else if verify && d.image? == some f then
            match ← Lean.PaperLean.OLeanPack.verifyImportImage file.toString with
            | "" => pure ", verified"
            | why => pure s!", not usable: {why}"
          else pure ""
        IO.println s!"  {f}: {showBytes md.byteSize.toNat}{stale}{verified}"
      else
        IO.println s!"  {f}: missing"
  for v in dataVars do
    IO.println s!"{v}: {(← IO.getEnv v).getD "(not set)"}"
  return 0

def clean (ws : Workspace) (names : List String) : LoggerIO UInt32 := do
  let dir := dataDir ws.dir
  let mut pkgs := #[]
  for n in names do
    match findPackage ws n with
    | .ok pkg => pkgs := pkgs.push pkg
    | .error e => IO.eprintln s!"paperlean: {e}. Nothing was deleted."; return 1
  if pkgs.isEmpty then
    let .ok md ← dir.symlinkMetadata.toBaseIO | do
      IO.println "There is no prepared data."
      return 0
    withDataLock dir do
      -- (a symbolic link in its place, as to a larger disk, stays for the next `prepare`)
      if md.type == .symlink && (← dir.isDir) then
        for e in ← dir.readDir do removePath e.path
      else
        removePath dir
    IO.println s!"Deleted the prepared data in {dir}."
    return 0
  unless ← dir.isDir do
    IO.println "There is no prepared data."
    return 0
  if pkgs.any (·.baseName == ws.root.baseName) then
    let msg ← withDataLock dir do
      match ← readPreparedData ws.dir with
      | some (.ok d) =>
        let roots := d.packs.filter (·.startsWith "root-")
        ({ d with packs := d.packs.filter (!·.startsWith "root-") }).install dir
        -- (`env.json` holds only paths `<directory>/<file>` of the data directory)
        for p in roots do removePath (dir / ((p.splitOn "/").headD ""))
        return s!"Deleted the pack of {ws.root.prettyName}."
      | some (.error e) =>
        PreparedData.empty.install dir
        return damagedNote e
      | none => return "There is no prepared data."
    IO.println msg
  let deps := pkgs.filter (·.baseName != ws.root.baseName)
  if deps.isEmpty then return 0
  cleanPackages ws deps

/-- The front end in elan's `bin`: the same for every version of PaperLean. It finds the Lake
workspace and the PaperLean toolchain for the Lean version of its `lean-toolchain` (the newest of
those installed), and runs that toolchain's `paperlean`, or says what is missing. The project keeps
its own toolchain, which plain `lake` commands use. `PAPERLEAN_TOOLCHAIN` (a toolchain name or path)
chooses another; a project whose toolchain is PaperLean uses it. `toolchain` is the PaperLean
toolchain that installed it, suggested for its Lean version. -/
def frontEnd (toolchain : String) : String := s!"#!/bin/sh
# The `paperlean` command: runs the PaperLean toolchain for the Lean version of the Lake workspace.
# Installed by `paperlean install`; the same for every version of PaperLean.
ELAN_HOME=$\{ELAN_HOME:-$HOME/.elan}
suggested='{toolchain}'
# `paperlean --version` where no toolchain can be chosen: the installed PaperLean toolchains
version=''
[ $# = 1 ] && case $1 in --version|version) version=1 ;; esac
installed() \{
  echo \"paperlean: $1; the installed PaperLean toolchains:\"
  n=0
  for d in \"$ELAN_HOME\"/toolchains/*; do
    [ -x \"$d/bin/paperlean\" ] || continue
    n=$((n + 1))
    echo \"  $(basename \"$d\" | sed 's|---|:|; s|--|/|')\"
  done
  [ $n -gt 0 ] && exit 0
  echo \"  none\"
  exit 1
}
dir=$(pwd -P)
ws=''
while :; do
  if [ -f \"$dir/lakefile.lean\" ] || [ -f \"$dir/lakefile.toml\" ]; then ws=$dir; break; fi
  [ \"$dir\" = / ] && break
  dir=$(dirname \"$dir\")
done
if [ -z \"$ws\" ]; then
  [ -n \"$version\" ] && installed \"not inside a Lake workspace\"
  echo \"paperlean: not inside a Lake workspace (no lakefile.lean or lakefile.toml in $(pwd) or above).\" >&2
  echo \"Run it in a Lake project.\" >&2
  exit 1
fi
tcdir_of() \{
  case $1 in
    /*) printf '%s' \"$1\" ;;
    *) printf '%s/toolchains/%s' \"$ELAN_HOME\" \"$(printf '%s' \"$1\" | sed 's|/|--|g; s|:|---|g')\" ;;
  esac
}
# the project's toolchain
dir=$ws
ptc=''
while :; do
  if [ -f \"$dir/lean-toolchain\" ]; then ptc=$(sed -n '1s/^[[:space:]]*//; 1s/[[:space:]]*$//p' \"$dir/lean-toolchain\"); break; fi
  [ \"$dir\" = / ] && break
  dir=$(dirname \"$dir\")
done
# as elan names it: a toolchain installed or linked under the name keeps it, a path too; otherwise a
# release of an origin, e.g. leanprover/lean4:v4.35.0-rc3 for 4.35.0-rc3
if [ -n \"$ptc\" ] && [ ! -e \"$ELAN_HOME/toolchains/$ptc\" ]; then
  case $ptc in
    /*) ;;
    *)
      case $ptc in
        *:*) origin=$\{ptc%%:*}; rel=$\{ptc#*:} ;;
        *) origin=leanprover/lean4; rel=$ptc ;;
      esac
      case $rel in
        nightly*) case $origin in *-nightly) ;; *) origin=$origin-nightly ;; esac ;;
        [0-9]*) rel=v$rel ;;
      esac
      ptc=$origin:$rel ;;
  esac
fi
tc=$\{PAPERLEAN_TOOLCHAIN:-}
if [ -z \"$tc\" ]; then
  if [ -z \"$ptc\" ]; then
    [ -n \"$version\" ] && installed \"the project in $ws has no lean-toolchain file\"
    echo \"paperlean: the project in $ws has no lean-toolchain file, so its Lean version is unknown.\" >&2
    exit 1
  fi
  if [ -x \"$(tcdir_of \"$ptc\")/bin/paperlean\" ]; then
    tc=$ptc
  else
    case $ptc in
      *:v*-lean*)
        # a PaperLean release that is not installed
        [ -n \"$version\" ] && installed \"the project's toolchain $ptc is not installed\"
        echo \"paperlean: the project's toolchain $ptc is not installed. Install it with:\" >&2
        echo \"  elan toolchain install $ptc\" >&2
        exit 1 ;;
    esac
    # the Lean version, e.g. 4.35.0-rc3 for leanprover/lean4:v4.35.0-rc3
    ver=$\{ptc##*:}
    ver=$\{ver#v}
    # the installed release for it of the newest PaperLean version, e.g.
    # qinz1yang--PaperLean---v0.1.0-lean4.35.0-rc3
    tc=$(ls -d \"$ELAN_HOME\"/toolchains/*-lean\"$ver\" 2>/dev/null |
      while read -r d; do [ -x \"$d/bin/paperlean\" ] && printf '%s\\t%s\\n' \"$\{d##*---v}\" \"$d\"; done |
      sort -V | tail -n 1 | cut -f 2-)
    if [ -z \"$tc\" ]; then
      [ -n \"$version\" ] && installed \"no PaperLean toolchain for Lean $ver (the project's toolchain is $ptc)\"
      echo \"paperlean: no PaperLean toolchain for Lean $ver (the project's toolchain is $ptc) is installed.\" >&2
      case $suggested in
        *-lean\"$ver\") echo \"Install it with:\" >&2; echo \"  elan toolchain install $suggested\" >&2 ;;
        *:*) echo \"Install the PaperLean release for Lean $ver, e.g.:\" >&2
             echo \"  elan toolchain install $\{suggested%%:*}:v<version>-lean$ver\" >&2 ;;
        *) echo \"Install the PaperLean release for Lean $ver with elan.\" >&2 ;;
      esac
      exit 1
    fi
  fi
fi
tcdir=$(tcdir_of \"$tc\")
if [ ! -x \"$tcdir/bin/paperlean\" ]; then
  echo \"paperlean: the toolchain $tc is not an installed PaperLean toolchain.\" >&2
  exit 1
fi
# Lake sees the toolchain that elan gives `lake` in the project, by which its downloads and caches
# are keyed, not this PaperLean one
export ELAN_HOME
if [ -n \"$ptc\" ]; then ELAN_TOOLCHAIN=$ptc; export ELAN_TOOLCHAIN; else unset ELAN_TOOLCHAIN; fi
cd \"$ws\" && exec \"$tcdir/bin/paperlean\" \"$@\"
"

def install : IO UInt32 := do
  let some home ← (do
      if let some h ← IO.getEnv "ELAN_HOME" then return some (FilePath.mk h)
      return (← IO.getEnv "HOME").map (FilePath.mk · / ".elan")) | do
    IO.eprintln "paperlean: neither ELAN_HOME nor HOME is set"; return 1
  let bin := home / "bin"
  unless ← bin.isDir do
    IO.eprintln s!"paperlean: {bin} does not exist; install elan first (https://github.com/leanprover/elan)."
    return 1
  -- this toolchain's name, as elan sets it for `lake`, else from the directory elan installed it in
  -- (the front end sets the project's toolchain); none if neither is a PaperLean release
  let toolchain ← do
    let tc := (← IO.getEnv "ELAN_TOOLCHAIN").getD ""
    if (paperleanVersionOf? tc).isSome then pure tc else
    let tc := match ((← IO.appDir).parent.bind (·.fileName)).getD "" |>.splitOn "---" with
      | [origin, ver] => s!"{origin.replace "--" "/"}:{ver}"
      | _ => ""
    pure (if (paperleanVersionOf? tc).isSome then tc else "")
  let file := bin / "paperlean"
  let tmp := bin / s!"paperlean.tmp.{← IO.Process.getPID}"
  IO.FS.writeFile tmp (frontEnd toolchain)
  IO.setAccessRights tmp {
    user := { read := true, write := true, execution := true }
    group := { read := true, execution := true }, other := { read := true, execution := true } }
  IO.FS.rename tmp file
  IO.println s!"Installed the paperlean command as {file}.\nA project keeps its Lean toolchain, which \
    `lake build` uses; in a project, `paperlean build` builds it with the PaperLean toolchain for its \
    Lean version."
  return 0

/-- Where the files of a `paperlean` command are: in `.lake`, and if that takes no new files in the root
package's build directory, which a compile of its modules writes to anyway. -/
def runDirs (ws : Workspace) : Array FilePath :=
  #[ws.dir / ".lake", ws.root.buildDir]

/-- A file to which the `lean` processes of the `paperlean` command of this process write, a side file
`<pfx><pid>.paperlean` of the first of `runDirs` that can have it, as what they write would be lost
otherwise; `none` if neither can. Removes what ended runs left, if it can. -/
def runFile (ws : Workspace) (pfx : String) : BaseIO (Option FilePath) := do
  for dir in runDirs ws do
    if let .ok entries ← dir.readDir.toBaseIO then
      for e in entries do
        if let some pid := (e.fileName.dropPrefix? pfx).bind
            (·.dropSuffix? ".paperlean") |>.bind (·.toString.toNat?) then
          unless ← Lean.PaperLean.processAlive pid.toUInt32 do
            discard <| (IO.FS.removeFile e.path).toBaseIO
  let pid ← IO.Process.getPID
  for dir in runDirs ws do
    discard <| (IO.FS.createDirAll dir).toBaseIO
    let file := dir / s!"{pfx}{pid}.paperlean"
    if ← writeSideFile file "" then
      return some file
  return none

/-- Runs `act`, a run of Lake for a `paperlean` command, with the file of this run (`runFile`) to which
its `lean` processes write their warnings about the prepared data (`PAPERLEAN_WARNINGS`), then reports
them; its exit code. On their standard error, Lake would keep them in its traces. -/
def withWarnings (ws : Workspace) (act : FilePath → IO UInt32) : IO UInt32 := do
  let file? ← runFile ws "paperlean-warnings-"
  -- (with no file, `lean` writes them to its standard error)
  let code ← act (file?.getD (ws.dir / ".lake" / "paperlean-warnings.paperlean"))
  if let some warnings := file? then
    if let .ok text ← (IO.FS.readFile warnings).toBaseIO then
      let n := (text.splitOn "\n").filter (!·.isEmpty) |>.length
      if n > 0 then
        IO.eprintln s!"paperlean: {n} warning(s) about the prepared data, in {warnings}; \
          `paperlean status` shows what is used"
      else
        discard <| (IO.FS.removeFile warnings).toBaseIO
  return code

/-- The variables with which Lake runs for a `paperlean` command: using prepared data and packing
(`accelerated`), with the file for the warnings of its `lean` processes (`withWarnings`). -/
def lakeVars (warnings : FilePath) : Array (String × Option String) :=
  #[(acceleratedVar, some "1"), ("PAPERLEAN_WARNINGS", some warnings.toString)]

/-- Runs this toolchain's `lake` with `args` in the workspace as `paperlean` commands do (`lakeVars`);
its exit code. -/
def spawnLake (ws : Workspace) (args : Array String) (env : Array (String × Option String))
    (warnings : FilePath) : IO UInt32 := do
  let env := env ++ lakeVars warnings
  let child ← IO.Process.spawn { cmd := ws.lakeEnv.lake.lake.toString, args, cwd := ws.dir, env }
  child.wait

/-- Runs this toolchain's `lake` with `args` in the workspace as `paperlean` commands do, then reports
the warnings of its `lean` processes about the prepared data (`withWarnings`); its exit code. -/
def runLake (ws : Workspace) (args : Array String) (env : Array (String × Option String) := #[]) :
    IO UInt32 :=
  withWarnings ws (spawnLake ws args env)

/-- Runs `act` with the variables that a Lake that `spawnLake` starts has: `lakeVars` and those of the
workspace's prepared data, which it sets on loading the workspace (`useWorkspaceData`); restores them
after. -/
def withLakeVars (ws : Workspace) (warnings : FilePath) (act : IO α) : IO α := do
  let names := (lakeVars warnings).map (·.1) ++ dataVars.push dataMarker
  let saved ← names.mapM fun n => return (n, ← IO.getEnv n)
  try
    for (n, v) in lakeVars warnings do Lean.PaperLean.setEnv n v
    useWorkspaceData ws.dir
    act
  finally
    for (n, v) in saved do Lean.PaperLean.setEnv n v

/-- Runs `lake build args` in this process with the loaded workspace (as `Lake.CLI.Main` does), if
it can do so as a Lake of its own would; its exit code, else `none`. -/
public abbrev BuildIn := Workspace → List String → BaseIO (Option UInt32)

/-- What of the dependencies ran in the interpreter in the imports of a build, from its statistics
`stats`: only an import can tell what it does with a module (`ReuseSummary.fallbacks`). What `prepare`
found says why of the modules that these name; of the others it is for `paperlean status` to say. -/
def interpretedSummary (ws : Workspace) (stats : String) : IO (Array String) := do
  let some (.ok d) ← readPreparedData ws.dir | return #[]
  if d.mismatch?.isSome || (← explicitDataVars) then return #[]
  let f := ReuseSummary.fallbacks stats
  let libs := d.libs.map (currentFindings ws)
  let reasons := ({} : Std.HashMap String String).insertMany (libs.flatMap fun l => l.interpreted ++ l.plugin)
  let importers := libs.foldl (·.insertMany ·.importers) ({} : Std.HashSet String)
  let packages := f.modules.filterMap fun (m, _) => (ws.findModule? m.toName).map (·.pkg.prettyName)
  let notBuilt := (← currentSummary ws d.libs d.summary).filter fun l =>
    l.contains ": not built (" && packages.any (l.startsWith s!"{·}: ")
  return notBuilt.map (s!"paperlean: no native library of {·}.") ++
    ReuseSummary.fallbackLines f reasons.get? importers.contains

/-- Runs `act` with the variables that have the `lean` processes of a build write their statistics and
what their imports did with native code to a file, then says what was not accelerated
(`Lake.PaperLean.ReuseSummary`, `interpretedSummary`). Statistics that the user asked for by the
variable go where the user said, and are not summarized. -/
def withReuseSummary (ws : Workspace) (act : IO α) : IO α := do
  let theirs := (← IO.getEnv "PAPERLEAN_REUSE_STATS").isSome
  let noSummary (why : String) : IO Unit :=
    IO.println s!"paperlean: no summary of what was not accelerated: {why}"
  let some stats ← runFile ws "paperlean-reuse-" | do
    let r ← act
    noSummary s!"no file can be written for it, in {" or ".intercalate ((runDirs ws).map (·.toString)).toList}"
    return r
  unless theirs do
    Lean.PaperLean.setEnv "PAPERLEAN_REUSE_STATS" (some stats.toString)
  -- (imports of this package's modules, which no library has, are no fallback; and without prepared
  -- data in use nothing is said about them)
  let inUse := match ← readPreparedData ws.dir with
    | some (.ok d) => d.mismatch?.isNone
    | _ => false
  if inUse && !(← explicitDataVars) then
    Lean.PaperLean.setEnv "PAPERLEAN_NATIVE_STATS" (some stats.toString)
    Lean.PaperLean.setEnv "PAPERLEAN_ROOT_PACKAGE" ws.root.id?
  try
    let r ← act
    match ← (IO.FS.readFile stats).toBaseIO with
    | .ok text =>
      unless theirs do
        (ReuseSummary.lines text ws.dir.toString).forM IO.println
      (← interpretedSummary ws text).forM IO.println
    | .error e => noSummary (toString e)
    return r
  finally
    unless theirs do
      Lean.PaperLean.setEnv "PAPERLEAN_REUSE_STATS" none
    Lean.PaperLean.setEnv "PAPERLEAN_NATIVE_STATS" none
    Lean.PaperLean.setEnv "PAPERLEAN_ROOT_PACKAGE" none
    try IO.FS.removeFile stats catch _ => pure ()

/-- Runs this toolchain's `lake` with `args` in the workspace as `lake` itself runs: for a command
whose prepared data cannot be protected (`withDataInUse`); its exit code. -/
def spawnPlainLake (ws : Workspace) (args : Array String) : IO UInt32 := do
  let env := #[(acceleratedVar, none)]
  let child ← IO.Process.spawn { cmd := ws.lakeEnv.lake.lake.toString, args, cwd := ws.dir, env }
  child.wait

/-- Runs `lake build args` for `paperlean build` as `runLake` does, but in this process if `buildIn`
can; its exit code. -/
def runBuild (ws : Workspace) (args : List String) (buildIn : BuildIn) : IO UInt32 :=
  withWarnings ws fun warnings => withReuseSummary ws do
    if let some code ← withLakeVars ws warnings (buildIn ws args) then
      return code
    spawnLake ws (#["build"] ++ args.toArray) #[] warnings

def build (ws : Workspace) (args : List String) (buildIn : BuildIn) : LoggerIO UInt32 := do
  let rebuild := args.contains "--rebuild-deps"
  -- `--prepare[=names]`: the root package by default
  let mut refreshRoot := false
  let mut prepareDeps : Array Package := #[]
  if let some a := args.find? fun a => a == "--prepare" || a.startsWith "--prepare=" then
    let names := ((a.drop "--prepare=".length).toString.splitOn ",").filter (!·.isEmpty)
    if names.isEmpty then refreshRoot := true
    for n in names do
      match findPackage ws n with
      | .ok pkg =>
        if pkg.baseName == ws.root.baseName then refreshRoot := true
        else unless prepareDeps.any (·.baseName == pkg.baseName) do prepareDeps := prepareDeps.push pkg
      | .error e => IO.eprintln s!"paperlean: {e}. Nothing was built."; return 1
  let args := args.filter fun a => a != "--rebuild-deps" &&
    a != "--prepare" && !a.startsWith "--prepare="
  let (mismatches, notes) ← dependencyMismatches ws
  if !mismatches.isEmpty && !rebuild then
    IO.eprintln s!"paperlean: the dependencies do not match PaperLean {Lean.PaperLean.version}, which is \
      built on Lean {upstreamVersion}:\n{"\n".intercalate (mismatches.map ("  " ++ ·)).toList}\n\
      Building now would rebuild them from source. Instead, either\n\
      - run `paperlean update`, which moves the dependencies to versions for one Lean version,\n\
      - revert the dependency to a version for Lean {upstreamVersion},\n\
      - build with official Lean (`lake build`), or\n\
      - run `paperlean build --rebuild-deps` to build anyway, rebuilding them with PaperLean.\n\
      Nothing was built."
    return 1
  for n in notes do IO.println s!"Note: {n}."
  let code ← withDataInUse (dataDir ws.dir) fun
    | some why => do
      IO.println s!"PaperLean prepared data: not used: {why}; building as `lake build` does."
      spawnPlainLake ws (#["build"] ++ args.toArray)
    | none => do
      IO.println s!"PaperLean prepared data: {← dataUse ws}{← staleNote ws}"
      -- the packs of builds that were interrupted, which only a build that packs would remove
      BuildData.removeEnded ws.dir
      runBuild ws args buildIn
  -- what was built is packed even if the build failed in part
  let mut result := code
  if !prepareDeps.isEmpty then
    IO.println s!"Preparing {", ".intercalate (prepareDeps.map (·.prettyName)).toList} again..."
    let c ← prepare ws { packages := some prepareDeps }
    if result == 0 then result := c
  if refreshRoot then
    let c ← refresh ws
    if result == 0 then result := c
  return result

def cacheGet (ws : Workspace) (args : List String) : LoggerIO UInt32 := do
  let cachePkgs := cachePackages ws
  if cachePkgs.size > 1 then
    IO.eprintln s!"paperlean: several packages provide a cache: \
      {", ".intercalate (cachePkgs.map (·.prettyName)).toList}; run the one you want with \
      `lake exe <package>/cache get`, then `paperlean prepare`."
    return 1
  if cachePkgs.isEmpty && args.isEmpty && !fromReservoir ws then
    IO.eprintln "paperlean: there is nothing to download: no package provides a cache, and none \
      comes from Reservoir, whose artifact cache `lake cache get` uses. Build the dependencies \
      with `lake build`, then run `paperlean prepare`."
    return 1
  let download (lakeArgs : Array String) := withDataInUse (dataDir ws.dir) (undone := "downloaded") fun
    | some why => do
      IO.println s!"paperlean: {why}; downloading as `lake` does."
      spawnPlainLake ws lakeArgs
    | none => runLake ws lakeArgs
  let code ← if h : cachePkgs.size = 1 then
      let pkg := cachePkgs[0]
      let lakeArgs := #["exe", s!"{pkg.prettyName}/cache", "get"] ++ args.toArray
      IO.println s!"Running {pkg.prettyName}'s cache: lake {" ".intercalate lakeArgs.toList}"
      download lakeArgs
    else do
      IO.println "No package provides a cache; running `lake cache get`."
      download (#["cache", "get"] ++ args.toArray)
  if code != 0 then
    IO.eprintln "paperlean: downloading failed; if nothing can be downloaded, build the dependencies \
      with `lake build`."
    return code
  prepare ws {}

/-- Runs `paperlean <args>` in the workspace of `config`, building with `buildIn` (`runBuild`); the
exit code. -/
public def cli (config : LoadConfig) (args : List String) (buildIn : BuildIn := fun _ _ => pure none) :
    LoggerIO UInt32 := do
  match args with
  | [] | ["help"] | ["--help"] | ["-h"] => IO.println usage; return 0
  | ["--version"] | ["version"] =>
    IO.println s!"PaperLean {Lean.PaperLean.version}"
    IO.println s!"Lean {Lean.versionString}, commit {Lean.githash}"
    IO.println s!"build {Lean.PaperLean.build}"
    return 0
  | ["install"] => install
  | cmd :: rest =>
    let known := ["prepare", "build", "cache", "status", "clean", "update"]
    unless known.contains cmd do
      IO.eprintln s!"paperlean: unknown command '{cmd}'\n{usage}"
      return 1
    let ws ← loadWorkspace config
    match cmd, rest with
    | "prepare", rest =>
      let mut root := false
      let mut native := true
      let mut jobs := 0
      let mut named : Option (Array Package) := none
      let mut rest := rest
      while !rest.isEmpty do
        match rest with
        | "--all" :: r => root := true; rest := r
        | "--no-native" :: r => native := false; rest := r
        | "-j" :: n :: r =>
          let some j := n.toNat? | IO.eprintln s!"paperlean: -j needs a number, not '{n}'"; return 1
          jobs := j; rest := r
        | n :: r =>
          if n.startsWith "-" then
            IO.eprintln s!"paperlean: unknown option '{n}'\n{usage}"; return 1
          match findPackage ws n with
          | .ok pkg =>
            let ps := named.getD #[]
            if pkg.baseName == ws.root.baseName then root := true
            named := some (if pkg.baseName == ws.root.baseName || ps.any (·.baseName == pkg.baseName) then ps
              else ps.push pkg)
          | .error e => IO.eprintln s!"paperlean: {e}. Nothing was changed."; return 1
          rest := r
        | [] => pure ()
      prepare ws { root, native, jobs, packages := named }
    | "build", rest => build ws rest buildIn
    | "cache", "get" :: rest => cacheGet ws rest
    | "status", [] => status ws
    | "status", ["--verify"] => status ws (verify := true)
    | "clean", names => clean ws names
    | "update", rest =>
      let mut pkgs := #[]
      for n in rest do
        match findPackage ws n with
        | .ok pkg => pkgs := pkgs.push pkg.baseName
        | .error e => IO.eprintln s!"paperlean: {e}. Nothing was changed."; return 1
      update ws pkgs
    | _, _ => IO.eprintln usage; return 1

end Lake.PaperLean
