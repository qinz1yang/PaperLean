/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import all Lake.PaperLean.Native
import all Lake.PaperLean.SourceInputs
import all Lake.PaperLean.SourceInputScope
import Lake.Config.Workspace
meta import Lake.Config.Package
meta import Lake.Config.Workspace
meta import Lake.Config.LakeConfig
meta import Lake.Config.Env
meta import Lake.Config.Cache
meta import Lake.PaperLean.Cache
meta import Lake.PaperLean.Env
meta import Lake.Build.Trace
open Lean Lake Lake.PaperLean System
private def pkg : Package := {(default : Package) with dir := ".", wsIdx := 0, depIdxs := #[]}
private def raw : Workspace.Raw := {
  lakeEnv := default, lakeCache := default, packages := #[pkg]
  lakeConfig := {config := default, defaultCacheService := .reservoirService "", defaultCacheUploadService? := none, cacheServices := {}}
}
private def ws : Workspace := {raw with
  size_packages_pos := by simp [raw]
  packages_wsIdx := by
    intro i h
    have hi : i < 1 := h
    have hi : i = 0 := by omega
    subst i
    rfl
  depIdxs_packages := by intro p hp i hi; simp [raw] at hp; subst p; simp [pkg] at hi
}
public def main : IO Unit := do
  let file ← IO.FS.realPath "Generated.c"
  let bytes ← IO.FS.readBinFile file
  let malformed := "#include <foreign.h>\n".toUTF8
  unless portableEmittedC bytes && !portableEmittedC malformed do
    throw <| IO.userError "wrong generated-C classifier result"
  unless (portableCSymbolGuard bytes #[]).isSome && (portableCSymbolGuard malformed #[]).isNone do
    throw <| IO.userError "wrong symbol guard"
  let (_, _, exports) ← cObjectNames file.toString
  unless exports.contains "l_bridgeFixture" do throw <| IO.userError "missing generated object name"
  let allowed ← canGroupCheckedC #[file.toString]
  let duplicate ← canGroupCheckedC #[file.toString, file.toString]
  unless allowed == Lean.PaperLean.nativeLibsAvailable && !duplicate do throw <| IO.userError "wrong C grouping"

  let [(id, hash)] := (← Lean.PaperLean.OLeanPack.hashFiles #[file.toString] #[file.parent.get!] "hashes" 1).toList
    | throw <| IO.userError "failed to fingerprint generated C"
  let hashes : FileHashes := (∅ : FileHashes).insert file.toString (id, hash)
  let descr : ArtifactDescr := {hash := Hash.ofByteArray bytes}
  let .ok (.ok (_, guarded)) ← ((checkArtifact hashes ".c" file (some descr)).run ⟨fun _ => pure ()⟩).toBaseIO
    | throw <| IO.userError "artifact verification failed"
  if guarded then throw <| IO.userError "unexpected custom C guard"

  let ctx : BuildContext := {opaqueWs := ws, registeredJobs := ← mkJobQueue, leanTrace := .nil, leanIncludeDirs := #[]}
  let opened ← Lake.PaperLean.SourceInputScope.withRun ctx true do
    discard <| Lake.PaperLean.SourceInputs.selectRead ctx file
    return (← Lake.PaperLean.SourceInputs.current? ctx).isSome
  let identity ← Lake.PaperLean.SourceInputs.readableIdentity file.toString
  unless opened == identity.isSome do throw <| IO.userError "source session failed to open"
  unless System.Platform.isWindows || identity.any (·.size == 56) do throw <| IO.userError "no regular-file identity"
  IO.println "interpreted C verification, grouping and source input passed"
