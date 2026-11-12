/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Config.FacetConfig
public import Lake.Build.Job.Monad
public import Lake.Build.Infos
import Lake.Util.Git
import Lake.Util.IO
import Lake.Util.Url
import Lake.Build.Common
import Lake.Build.Targets
import Lake.Build.Job.Register
import Lake.Reservoir

/-! # Package Facet Builds
Build function definitions for a package's builtin facets.
-/

open System
namespace Lake
open Lean (Name)

/-- Fetch the package's direct dependencies. -/
def Package.recFetchDeps (self : Package) : FetchM (Job (Array Package)) := do
  return Job.pure self.depPkgs

/-- The `PackageFacetConfig` for the builtin `depsFacet`. -/
public def Package.depsFacetConfig : PackageFacetConfig depsFacet :=
  mkFacetJobConfig recFetchDeps (buildable := false)

/-- Compute a topological ordering of the package's transitive dependencies. -/
def Package.recComputeTransDeps (self : Package) : FetchM (Job (Array Package)) := ensureJob do
  (pure ·.toArray) <$> self.depPkgs.foldlM (init := OrdPackageSet.empty) fun deps dep => do
    let depDeps ← (← fetch <| dep.transDeps).await
    return depDeps.foldl (·.insert ·) deps |>.insert dep

/--
Collects the Lean modules of the package's default targets: the modules of each default library,
and the root of each default executable together with its local transitive imports. A default
target that builds no Lean modules, such as a custom target, contributes nothing.
-/
def Package.recCollectDefaultModules (self : Package) : FetchM (Job (Array Module)) := ensureJob do
  let mut mods := #[]
  let mut seen : ModuleSet := ∅
  for target in self.defaultTargets do
    let targetMods ←
      if let some lib := self.findLeanLib? target then
        (← lib.modules.fetch).await
      else if let some exe := self.findLeanExe? target then
        let imports ← (← exe.root.transImports.fetch).await
        pure <| imports.push exe.root
      else
        pure #[]
    for mod in targetMods do
      unless seen.contains mod do
        seen := seen.insert mod
        mods := mods.push mod
  return Job.pure mods

/-- The `PackageFacetConfig` for the builtin `defaultModulesFacet`. -/
public def Package.defaultModulesFacetConfig : PackageFacetConfig defaultModulesFacet :=
  mkFacetJobConfig Package.recCollectDefaultModules (buildable := false)

/-- The `PackageFacetConfig` for the builtin `transDepsFacet`. -/
public def Package.transDepsFacetConfig : PackageFacetConfig transDepsFacet :=
  mkFacetJobConfig recComputeTransDeps (buildable := false)

/--
Tries to download and unpack the package's cached build archive
(e.g., from Reservoir or GitHub).
-/
def Package.fetchOptBuildCacheCore (self : Package) : FetchM (Job Bool) := do
  if self.preferReleaseBuild then
    self.optGitHubRelease.fetch
  else
    self.optReservoirBarrel.fetch

/-- The `PackageFacetConfig` for the builtin `optBuildCacheFacet`. -/
public def Package.optBuildCacheFacetConfig : PackageFacetConfig optBuildCacheFacet :=
  mkFacetJobConfig (·.fetchOptBuildCacheCore)

/- Best-effort cleanup: a failed removal of optional cache state must not abort
the build. -/
private def bestEffort (act : IO Unit) : IO Unit :=
  try act catch _ => pure ()

/- Marker written before a build archive is unpacked and removed only after the
unpack completes.  It is outside the build directory so `lake pack` cannot
capture it. -/
private def Package.cacheUnpackPendingFile (self : Package) : FilePath :=
  FilePath.join self.lakeDir (FilePath.mk "build-cache-unpack.pending")

/- Staging directory used while unpacking, next to (not inside) the build
directory so a partial extraction is never mistaken for a build. -/
private def Package.cacheUnpackStagingDir (self : Package) : FilePath :=
  self.buildDir.withFileName <|
    (self.buildDir.fileName.getD "build") ++ ".unpack"

/- Moves `dir` aside to the first unused `<dir>.partial-<n>` next to it; `false` if that fails. A
directory whose contents cannot be removed (e.g. a subdirectory without write permission) can still be
renamed within its parent. -/
private def quarantineDir (dir : FilePath) : IO Bool := do
  let base := dir.fileName.getD "build"
  for n in [1:101] do
    let dest := dir.withFileName s!"{base}.partial-{n}"
    unless ← dest.pathExists do
      try
        IO.FS.rename dir dest
        return true
      catch _ =>
        return false
  return false

/- Discards what a failed or interrupted build-cache unpack may have left before the package is built
from source: its build and staging directories are removed or, if that fails, moved aside. Only once
neither directory is left is the pending marker deleted. Otherwise the marker stays, so that no later
build takes the partial tree for a complete one, and the error says what to remove; the build must not
go on to read it. `none` if all went well. -/
private def Package.discardPartialUnpack (self : Package) : IO (Option String) := do
  let mut left : Array String := #[]
  for dir in #[self.buildDir, self.cacheUnpackStagingDir] do
    try
      removeDirAllIfExists dir
    catch e =>
      unless ← quarantineDir dir do
        left := left.push s!"'{dir}' ({e})"
  unless left.isEmpty do
    return some s!"the build cache of '{self.baseName}' was not unpacked completely, and its partial \
      build files could not be removed or moved aside: {", ".intercalate left.toList}; remove them, \
      then build again"
  try
    removeFileIfExists self.cacheUnpackPendingFile
    return none
  catch e =>
    return some s!"could not remove '{self.cacheUnpackPendingFile}' after discarding the partial build \
      cache of '{self.baseName}' ({e})"

/-- Tries to download the package's build cache (if configured). -/
def Package.maybeFetchBuildCache (self : Package) : FetchM (Job Bool) := do
  let pendingFile := self.cacheUnpackPendingFile
  let stagingDir := self.cacheUnpackStagingDir
  let attemptPending ← pendingFile.pathExists
  let buildDirExists ← self.buildDir.pathExists
  let shouldFetch :=
    (← getTryCache) &&
    -- A pending marker asks for a retry even when the build directory exists:
    -- the previous unpack did not complete.  An existing directory without a
    -- marker is still never clobbered automatically.
    (attemptPending || !buildDirExists) &&
    (self.preferReleaseBuild || -- GitHub release
      ((self.scope == "leanprover" || self.scope == "leanprover-community")
        && !(← getElanToolchain).isEmpty)) -- Reservoir
  if shouldFetch then
    if attemptPending then
      -- A previous attempt left a staging tree; the build tree itself may also
      -- be partial.  `fetchBuildArchive` removes the stale archive/trace and
      -- extracts only after a successful download.
      bestEffort (removeDirAllIfExists stagingDir)
    self.optBuildCache.fetch
  else
    if attemptPending then
      -- No cache will be fetched (`--no-cache`, or the package is ineligible),
      -- so the fallback source build must not trust a partially unpacked tree.
      if let some msg ← self.discardPartialUnpack then
        error msg
    return pure true

@[inline]
def Package.optFacetDetails (self : Package) (facet : Name) : JobM String := do
  if (← getIsVerbose) then
    return s!" (see '{self.baseName}:{Name.eraseHead facet}' for details)"
  else
    return " (run with '-v' for details)"

/--
Tries to download and unpack the package's cached build archive
(e.g., from Reservoir or GitHub). Prints a warning on failure.
-/
def Package.maybeFetchBuildCacheWithWarning (self : Package) := do
  let job ← self.maybeFetchBuildCache
  job.mapM fun success => do
    unless success do
      -- The retry (or the first attempt) failed after a marker was written.
      -- Do not let the fallback source build trust the possibly partial tree.
      if (← self.cacheUnpackPendingFile.pathExists) then
        if let some msg ← self.discardPartialUnpack then
          error msg
      if self.preferReleaseBuild then
        let details ← self.optFacetDetails optGitHubReleaseFacet
        logWarning s!"building from source; failed to fetch GitHub release{details}"
      else
        let details ← self.optFacetDetails optReservoirBarrelFacet
        logVerbose s!"building from source; failed to fetch Reservoir build{details}"

/--
Build the `extraDepTargets` for the package.
Also, if the package is a dependency, maybe fetch its build cache.
-/
def Package.recBuildExtraDepTargets (self : Package) : FetchM (Job Unit) :=
  withRegisterJob s!"{self.baseName}:extraDep" do
  let mut job := Job.nil s!"@{self.baseName}:extraDep"
  -- Fetch build cache if this package is a dependency
  unless self.isRoot do
    job := job.add (← self.maybeFetchBuildCacheWithWarning)
  -- Build this package's extra dep targets
  for target in self.extraDepTargets do
    job := job.mix (← self.fetchTargetJob target)
  return job

/-- The `PackageFacetConfig` for the builtin `dynlibFacet`. -/
public def Package.extraDepFacetConfig : PackageFacetConfig extraDepFacet :=
  mkFacetJobConfig Package.recBuildExtraDepTargets

/-- Compute the package's Reservoir barrel URL. -/
def Package.getBarrelUrl (self : Package) : JobM String := do
  if self.scope.isEmpty then
    error "package has no Reservoir scope"
  let repo := GitRepo.mk self.dir
  let some rev ← repo.getHeadRevision?
    | error "failed to resolve HEAD revision"
  let env ← getLakeEnv
  let mut url := Reservoir.pkgApiUrl env self.scope self.reservoirName
  if env.toolchain.isEmpty then
    error "Lean toolchain not known; Reservoir only hosts builds for known toolchains"
  url := s!"{url}/barrel?rev={rev}&toolchain={uriEncode env.toolchain}"
  return url

/-- Compute the package's GitHub release URL. -/
def Package.getReleaseUrl (self : Package) : JobM String := do
  let repo := GitRepo.mk self.dir
  let repoUrl? := self.releaseRepo? <|> self.remoteUrl?
  let some repoUrl := repoUrl? <|> (← repo.getFilteredRemoteUrl?)
    | error "release repository URL not known; \
        the package may need to set 'releaseRepo'"
  let some tag ← repo.findTag?
    | let rev ← if let some rev ← repo.getHeadRevision? then pure s!" '{rev}'" else pure ""
      error s!"no release tag found for revision{rev}"
  return s!"{repoUrl}/releases/download/{tag}/{self.buildArchive}"

/-- Tries to download and unpack a build archive for the package from a URL. -/
def Package.fetchBuildArchive
  (self : Package) (url : String) (archiveFile : FilePath)
  (headers : Array String := #[])
: JobM PUnit := do
  let depTrace := Hash.ofString url
  let traceFile := archiveFile.addExtension "trace"
  let pendingFile := self.cacheUnpackPendingFile
  let stagingDir := self.cacheUnpackStagingDir
  let pendingBefore ← pendingFile.pathExists
  if pendingBefore then
    -- A previous unpack did not complete.  Its staging tree and the archive it
    -- may have failed on are not reusable.  Keep the old build tree: a
    -- successful extraction overlays it, and a failed one is removed by the
    -- caller before falling back to source.
    bestEffort (removeDirAllIfExists stagingDir)
    bestEffort (removeFileIfExists traceFile)
    bestEffort (removeFileIfExists archiveFile)
  let upToDate ← buildUnlessUpToDate? (action := .fetch) archiveFile depTrace traceFile do
    download url archiveFile headers
  let buildDirExists ← self.buildDir.pathExists
  -- A pending marker overrides `upToDate && buildDirExists`: that tree is not
  -- proof of the new archive's complete unpack.
  unless (upToDate && buildDirExists) && !pendingBefore do
    updateAction .unpack
    createParentDirs pendingFile
    IO.FS.writeFile pendingFile ""
    try
      if buildDirExists then
        untar archiveFile self.buildDir
      else
        -- Extract next to the build directory, which it becomes only once
        -- complete.  The existence of the build directory is what this
        -- function and `maybeFetchBuildCache` take for a complete unpack.
        -- (Not best-effort: extracting over files left by an earlier attempt
        -- would publish them as part of the build.)
        removeDirAllIfExists stagingDir
        untar archiveFile stagingDir
        IO.FS.rename stagingDir self.buildDir
      bestEffort (removeFileIfExists pendingFile)
    catch e =>
      -- Keep the marker: the next cache attempt must retry.  Discard a partial
      -- staging tree and the archive that failed to unpack so a retry downloads
      -- again rather than reusing it.
      bestEffort (removeDirAllIfExists stagingDir)
      bestEffort (removeFileIfExists traceFile)
      bestEffort (removeFileIfExists archiveFile)
      throw e

@[inline]
def Package.mkOptBuildArchiveFacetConfig
  {facet : Name} (archiveFile : Package → FilePath)
  (getUrl : Package → JobM String) (headers : Array String := #[])
  [FamilyDef FacetOut facet Bool]
: PackageFacetConfig facet := mkFacetJobConfig fun pkg =>
  withRegisterJob s!"{pkg.baseName}:{Name.eraseHead facet}" (optional := true) <| Job.async do
  try
    let url ← getUrl pkg
    pkg.fetchBuildArchive url (archiveFile pkg) headers
    return true
  catch _ =>
    updateAction .fetch
    return false

@[inline]
def Package.mkBuildArchiveFacetConfig
  {facet : Name} (optFacet : Name) (what : String)
  [FamilyDef FacetOut facet Unit]
  [FamilyDef FacetOut optFacet Bool]
: PackageFacetConfig facet :=
  mkFacetJobConfig fun pkg =>
    withRegisterJob s!"{pkg.baseName}:{Name.eraseHead facet}" do
      (← fetch <| pkg.facetCore optFacet).mapM fun success => do
        unless success do
          error s!"failed to fetch {what}{← pkg.optFacetDetails optFacet}"

/-- The `PackageFacetConfig` for the builtin `buildCacheFacet`. -/
public def Package.buildCacheFacetConfig : PackageFacetConfig buildCacheFacet :=
  mkBuildArchiveFacetConfig optBuildCacheFacet "build cache"

/-- The `PackageFacetConfig` for the builtin `optReservoirBarrelFacet`. -/
public def Package.optBarrelFacetConfig : PackageFacetConfig optReservoirBarrelFacet :=
  mkOptBuildArchiveFacetConfig barrelFile getBarrelUrl Reservoir.lakeHeaders

/-- The `PackageFacetConfig` for the builtin `reservoirBarrelFacet`. -/
public def Package.barrelFacetConfig : PackageFacetConfig reservoirBarrelFacet :=
  mkBuildArchiveFacetConfig optReservoirBarrelFacet "Reservoir build"

/-- The `PackageFacetConfig` for the builtin `optGitHubReleaseFacet`. -/
public def Package.optGitHubReleaseFacetConfig : PackageFacetConfig optGitHubReleaseFacet :=
  mkOptBuildArchiveFacetConfig buildArchiveFile getReleaseUrl

/-- The `PackageFacetConfig` for the builtin `gitHubReleaseFacet`. -/
public def Package.gitHubReleaseFacetConfig : PackageFacetConfig gitHubReleaseFacet :=
  mkBuildArchiveFacetConfig optGitHubReleaseFacet "GitHub release"

/--
Perform a build job after first checking for an (optional) cached build
for the package (e.g., from Reservoir or GitHub).
-/
public def Package.afterBuildCacheAsync (self : Package) (build : JobM (Job α)) : FetchM (Job α) := do
  if self.isRoot then
    build
  else
    (← self.maybeFetchBuildCache).bindM fun _ => do
      setTrace nilTrace -- ensure both branches start with the same trace
      build

/--
 Perform a build after first checking for an (optional) cached build
 for the package (e.g., from Reservoir or GitHub).
-/
public def Package.afterBuildCacheSync (self : Package) (build : JobM α) : FetchM (Job α) := do
  if self.isRoot then
    Job.async build
  else
    (← self.maybeFetchBuildCache).mapM fun _  => do
      setTrace nilTrace -- ensure both branches start with the same trace
      build

/--
A name-configuration map for the initial set of
Lake package facets (e.g., `extraDep`).
-/
public def Package.initFacetConfigs : DNameMap PackageFacetConfig :=
  DNameMap.empty
  |>.insert depsFacet depsFacetConfig
  |>.insert transDepsFacet transDepsFacetConfig
  |>.insert defaultModulesFacet defaultModulesFacetConfig
  |>.insert extraDepFacet extraDepFacetConfig
  |>.insert optBuildCacheFacet optBuildCacheFacetConfig
  |>.insert buildCacheFacet buildCacheFacetConfig
  |>.insert optReservoirBarrelFacet optBarrelFacetConfig
  |>.insert reservoirBarrelFacet barrelFacetConfig
  |>.insert optGitHubReleaseFacet optGitHubReleaseFacetConfig
  |>.insert gitHubReleaseFacet gitHubReleaseFacetConfig

@[inherit_doc Package.initFacetConfigs]
public abbrev initPackageFacetConfigs := Package.initFacetConfigs
