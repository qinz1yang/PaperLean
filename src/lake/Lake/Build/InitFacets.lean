/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Config.FacetConfig
import Lake.Build.Module
import Lake.Build.Package
import Lake.Build.Library
import Lake.Build.Executable
import Lake.Build.ExternLib
import Lake.Build.InputFile
import Lake.PaperLean.BuiltinFacets

/-! # Initial Facets -/

namespace Lake

/-- The initial set of Lake facets. -/
public def initFacetConfigs : FacetConfigMap :=
  DNameMap.empty
  |> insert Module.initFacetConfigs
  |> insert Package.initFacetConfigs
  |> insert LeanLib.initFacetConfigs
  |> insert LeanExe.initFacetConfigs
  |> insert ExternLib.initFacetConfigs
  |> insert InputFile.initFacetConfigs
  |> insert InputDir.initFacetConfigs
where
  insert {k} (group : DNameMap (KFacetConfig k)) map :=
    group.foldl (init := map) fun m _ v => m.insert v.toFacetConfig

-- The interpreter may evaluate a closed definition in separate environments.
-- Select the same immutable provider objects for stock workspace loading and
-- for recognizing them when PaperLean writes a shared setup.
public initialize PaperLean.workspaceInitFacets : FacetConfigMap ← do
  let facets := initFacetConfigs
  PaperLean.builtinFacetMap.set (some facets)
  return facets
