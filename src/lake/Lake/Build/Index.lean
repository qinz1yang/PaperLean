/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Build.Fetch
import Lake.Config.Monad
import Lake.Build.Topological
import Lake.Util.StoreInsts

/-!
# The Lake Build Index

The Lake build index is the complete map of Lake build keys to
Lake build functions, which is used by Lake to build any Lake build info.

This module leverages the index to perform topologically-based recursive builds.
-/

open Lean (Name)
open System (FilePath)

namespace Lake

private def cacheJob (certified : Bool) (info : BuildInfo) (produce : FetchM (Job (BuildData info.key))) :
    FetchM (Job (BuildData info.key)) := do
  unless certified do return ← fetchOrCreate info.key produce
  if let some job ← fetch? info.key then return job
  let job ← produce
  PaperLean.saveSetupJob info job

/-- Recursive build function for anything in the Lake build index. -/
private def recBuildCore (certified : Bool) (info : BuildInfo) : FetchM (Job (BuildData info.key)) :=
  match info with
  | .target pkg target => do
    if let some decl := pkg.findTargetDecl? target then
      if h : decl.kind.isAnonymous then
        cacheJob certified (.target pkg target) do (decl.targetConfig h).fetchFn pkg
      else
        let kind := ⟨decl.kind, by simp [decl.target_eq_type h]⟩
        let job := Job.pure (kind := kind) <| decl.mkConfigTarget pkg
        return cast (by simp [decl.data_eq_target h]) job
    else
      error s!"invalid target '{info}': target not found in package"
  | .facet target kind data facet => do
    if let some config := (← getWorkspace).findFacetConfig? facet then
      if h : config.kind = kind then
        let recFetch := do
          if certified then PaperLean.observeSetupProvider info facet
          config.fetchFn <| cast (by simp [h]) data
        if config.memoize then
          cacheJob certified (.facet target kind data facet) recFetch
        else
          recFetch
      else
        error s!"invalid target '{info}': \
          input target is of kind '{kind}', but facet expects '{config.kind}'"
    else
      error s!"invalid target '{info}': unknown facet '{facet}'"

/-- Direct use under an arbitrary fetch function performs ordinary Lake memoization. -/
def recBuildWithIndex (info : BuildInfo) : FetchM (Job (BuildData info.key)) :=
  recBuildCore false info

/-- Recursive build function with memoization. Only this engine constructs the
stack-bound recursive dispatch passed to builtin providers. -/
def recFetchWithIndex : (info : BuildInfo) → RecBuildM (Job (BuildData info.key)) :=
 inline <| recFetchAcyclic (β := (Job <| BuildData ·.key)) BuildInfo.key (recBuildCore true)

/--
Run a recursive Lake build using the Lake build index
and a topological / suspending scheduler.
-/
@[inline] public nonrec def FetchT.run (x : FetchT m α) : RecBuildT m α :=
  x.run recFetchWithIndex

private def recFetchPlain : (info : BuildInfo) → RecBuildM (Job (BuildData info.key)) :=
  inline <| recFetchAcyclic (β := (Job <| BuildData ·.key)) BuildInfo.key (recBuildCore false)

/-- Select the normal memoizing dispatcher once for a run without shared setups.
The public recursive runner remains valid for standalone callers. -/
@[inline] public def PaperLean.runFetchFor (track : Bool) (x : FetchT m α) : RecBuildT m α :=
  if track then FetchT.run x else
    EquipT.run x recFetchPlain
