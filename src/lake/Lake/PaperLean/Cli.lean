/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
import Init
public import Lake.Load.Config
import Lake.Load.Workspace
import Lake.Config.LeanExe
import Lake.Util.Lock
import Lake.PaperLean.Env
import Lake.PaperLean.Prepare
import Lake.PaperLean.Update
import Lean.PaperLean.System
import Lean.PaperLean.OLeanPack

/-!
The `paperlean` command (`lake paperlean`, run by the toolchain's `bin/paperlean`, which the front end
in elan's `bin` runs for the Lean version of a project: `frontEnd`). A project keeps official Lean as
its toolchain, which `lake build` and the editor use; `paperlean build` and the other commands run
this toolchain's Lake with prepared data and packing (`runLake`).
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
  build [--rebuild-deps] [--lean-heartbeats] [--prepare[=names]] [lake arguments]
                            check the dependencies, report whether prepared data is used, then run
                            `lake build`; with --lean-heartbeats, heartbeats are counted as by Lean
                            (use it before submitting code to a project that builds with Lean);
                            with --prepare, pack the root package's modules that changed afterwards
                            (named dependencies are prepared again in full)
  cache get [arguments]     download built dependencies, then prepare them
  update [names]            update the dependencies if a PaperLean for the Lean version they then
                            need is available, then prepare them; nothing changes otherwise
  status [--verify]         show the prepared data and whether Lean uses it; with --verify, also
                            read the packs whole to check that they are as written
  clean [names]             delete prepared data: all of it, or that of the named packages and of
                            the prepared packages that depend on them
  install                   install or update the `paperlean` front end in elan's `bin`
  --version                 print PaperLean's version"

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

/-- Why the built dependencies do not match this PaperLean, if they do not: a dependency that asks for
another Lean release, or whose `.olean` files another Lean built. -/
def dependencyMismatches (ws : Workspace) : IO (Array String) := do
  let mut out := #[]
  for pkg in dependencies ws do
    let tcFile := pkg.dir / "lean-toolchain"
    if ← tcFile.pathExists then
      let v := toolchainVersion (← IO.FS.readFile tcFile)
      if v != upstreamVersion then
        out := out.push s!"{pkg.prettyName} asks for Lean {v} (its lean-toolchain)"
    if ← pkg.leanLibDir.isDir then
      if let some f := (← pkg.leanLibDir.walkDir).find? (·.extension == some "olean") then
        if let some gh ← oleanGithash? f then
          if gh != Lean.githash then
            out := out.push s!"{pkg.prettyName} was built by another Lean (githash {gh.take 12})"
  return out

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

def status (ws : Workspace) (verify := false) : IO UInt32 := do
  IO.println s!"PaperLean {Lean.PaperLean.version} (Lean {Lean.versionString}, {Lean.githash})"
  IO.println s!"workspace: {ws.dir}"
  IO.println s!"prepared data ({dataDir ws.dir}): {← dataUse ws}"
  if let some (.ok d) ← readPreparedData ws.dir then
    let prepared := if d.mismatch?.isNone then preparedPackages ws d else #[]
    for pkg in dependencies ws do
      IO.println s!"  package {pkg.prettyName}: \
        {if prepared.contains (pkgKey pkg) then "prepared" else "not prepared"}"
    for line in d.summary do
      IO.println s!"  native library of {line}"
    for f in d.packs ++ d.image?.toArray ++ d.native do
      let file := dataDir ws.dir / f
      if ← file.pathExists then
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
          else pure ""
        IO.println s!"  {f}: {showBytes (← file.metadata).byteSize.toNat}{stale}{verified}"
      else
        IO.println s!"  {f}: missing"
  for v in dataVars do
    IO.println s!"{v}: {(← IO.getEnv v).getD "(not set)"}"
  if (← IO.getEnv "PAPERLEAN_HEARTBEATS") == some "lean" then
    IO.println "PAPERLEAN_HEARTBEATS=lean: heartbeats are counted as by Lean (native code is off)"
  return 0

def clean (ws : Workspace) (names : List String) : LoggerIO UInt32 := do
  let dir := dataDir ws.dir
  let mut pkgs := #[]
  for n in names do
    match findPackage ws n with
    | .ok pkg => pkgs := pkgs.push pkg
    | .error e => IO.eprintln s!"paperlean: {e}. Nothing was deleted."; return 1
  unless ← dir.isDir do
    IO.println "There is no prepared data."
    return 0
  if pkgs.isEmpty then
    withDataLock dir do
      IO.FS.removeDirAll dir
    IO.println s!"Deleted the prepared data in {dir}."
    return 0
  if pkgs.any (·.baseName == ws.root.baseName) then
    withDataLock dir do
      match ← readPreparedData ws.dir with
      | some (.ok d) =>
        let roots := d.packs.filter (·.startsWith "root-")
        let d := { d with packs := d.packs.filter (!·.startsWith "root-") }
        d.write (dir / "env.json.tmp")
        IO.FS.rename (dir / "env.json.tmp") (dir / "env.json")
        for p in roots do
          if let some parent := (dir / p).parent then
            if ← parent.isDir then IO.FS.removeDirAll parent
      | _ => pure ()
    IO.println s!"Deleted the pack of {ws.root.prettyName}."
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
dir=$(pwd -P)
ws=''
while :; do
  if [ -f \"$dir/lakefile.lean\" ] || [ -f \"$dir/lakefile.toml\" ]; then ws=$dir; break; fi
  [ \"$dir\" = / ] && break
  dir=$(dirname \"$dir\")
done
if [ -z \"$ws\" ]; then
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
tc=$\{PAPERLEAN_TOOLCHAIN:-}
if [ -z \"$tc\" ]; then
  dir=$ws
  ptc=''
  while :; do
    if [ -f \"$dir/lean-toolchain\" ]; then ptc=$(sed -n '1s/[[:space:]]*$//p' \"$dir/lean-toolchain\"); break; fi
    [ \"$dir\" = / ] && break
    dir=$(dirname \"$dir\")
  done
  if [ -z \"$ptc\" ]; then
    echo \"paperlean: the project in $ws has no lean-toolchain file, so its Lean version is unknown.\" >&2
    exit 1
  fi
  if [ -x \"$(tcdir_of \"$ptc\")/bin/paperlean\" ]; then
    tc=$ptc
  else
    # the Lean version, e.g. 4.35.0-rc3 for leanprover/lean4:v4.35.0-rc3
    ver=$\{ptc##*:}
    ver=$\{ver#v}
    # the newest installed release for it, e.g. qinz1yang--PaperLean---v0.1.0-lean4.35.0-rc3
    tc=$(ls -d \"$ELAN_HOME\"/toolchains/*-lean\"$ver\" 2>/dev/null | sort -V |
      while read -r d; do [ -x \"$d/bin/paperlean\" ] && echo \"$d\"; done | tail -n 1)
    if [ -z \"$tc\" ]; then
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
# its name, as elan would set it, e.g. qinz1yang/PaperLean:v0.1.0-lean4.35.0-rc3
case $tc in
  /*) name=$(basename \"$tc\")
      case $name in
        *---*) ELAN_TOOLCHAIN=$(printf '%s' \"$\{name%%---*}\" | sed 's|--|/|'):$\{name#*---}; export ELAN_TOOLCHAIN ;;
        *) unset ELAN_TOOLCHAIN ;;
      esac ;;
  *) ELAN_TOOLCHAIN=$tc; export ELAN_TOOLCHAIN ;;
esac
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
  let toolchain := (← IO.getEnv "ELAN_TOOLCHAIN").getD ""
  let file := bin / "paperlean"
  IO.FS.writeFile (bin / "paperlean.tmp") (frontEnd toolchain)
  IO.setAccessRights (bin / "paperlean.tmp") {
    user := { read := true, write := true, execution := true }
    group := { read := true, execution := true }, other := { read := true, execution := true } }
  IO.FS.rename (bin / "paperlean.tmp") file
  IO.println s!"Installed the paperlean command as {file}.\nA project keeps its Lean toolchain, which \
    `lake build` uses; in a project, `paperlean build` builds it with the PaperLean toolchain for its \
    Lean version."
  return 0

/-- Runs this toolchain's `lake` with `args` in the workspace, using prepared data and packing as
`paperlean` commands do (`accelerated`); its exit code. -/
def runLake (ws : Workspace) (args : Array String) (env : Array (String × Option String) := #[]) :
    IO UInt32 := do
  let env := env.push (acceleratedVar, some "1")
  let child ← IO.Process.spawn { cmd := ws.lakeEnv.lake.lake.toString, args, cwd := ws.dir, env }
  return (← child.wait)

def build (ws : Workspace) (args : List String) : LoggerIO UInt32 := do
  let rebuild := args.contains "--rebuild-deps"
  let leanHeartbeats := args.contains "--lean-heartbeats"
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
  let args := args.filter fun a => a != "--rebuild-deps" && a != "--lean-heartbeats" &&
    a != "--prepare" && !a.startsWith "--prepare="
  let mismatches ← dependencyMismatches ws
  if !mismatches.isEmpty && !rebuild then
    IO.eprintln s!"paperlean: the dependencies do not match PaperLean {Lean.PaperLean.version}, which is \
      built on Lean {upstreamVersion}:\n{"\n".intercalate (mismatches.map ("  " ++ ·)).toList}\n\
      Building now would rebuild them from source. Instead, either\n\
      - run `paperlean update`, which moves the dependencies to versions for one Lean version,\n\
      - revert the dependency to a version for Lean {upstreamVersion},\n\
      - build with official Lean (`lake build`), or\n\
      - run `paperlean build --rebuild-deps` to rebuild the dependencies with PaperLean.\n\
      Nothing was built."
    return 1
  IO.println s!"PaperLean prepared data: {← dataUse ws}{← staleNote ws}"
  let code ← if leanHeartbeats then
      IO.println "Heartbeats are counted as by Lean: native code and the interpreters' shared entries are off."
      runLake ws (#["build"] ++ args.toArray) #[("PAPERLEAN_HEARTBEATS", some "lean")]
    else
      runLake ws (#["build"] ++ args.toArray)
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
  let code ← if h : cachePkgs.size = 1 then
      let pkg := cachePkgs[0]
      let lakeArgs := #["exe", s!"{pkg.prettyName}/cache", "get"] ++ args.toArray
      IO.println s!"Running {pkg.prettyName}'s cache: lake {" ".intercalate lakeArgs.toList}"
      runLake ws lakeArgs
    else do
      IO.println "No package provides a cache; running `lake cache get`."
      runLake ws (#["cache", "get"] ++ args.toArray)
  if code != 0 then
    IO.eprintln "paperlean: downloading failed; if nothing can be downloaded, build the dependencies \
      with `lake build`."
    return code
  prepare ws {}

/-- Runs `paperlean <args>` in the workspace of `config`; the exit code. -/
public def cli (config : LoadConfig) (args : List String) : LoggerIO UInt32 := do
  match args with
  | [] | ["help"] | ["--help"] | ["-h"] => IO.println usage; return 0
  | ["--version"] | ["version"] =>
    IO.println s!"PaperLean {Lean.PaperLean.version}"; return 0
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
    | "build", rest => build ws rest
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
