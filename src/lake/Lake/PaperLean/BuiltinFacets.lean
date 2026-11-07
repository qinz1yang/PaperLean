/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lake.Config.FacetConfig

namespace Lake.PaperLean
/-- The facet map used by Lake itself. A consumer that has not loaded Lake’s builtin
providers leaves the index disabled. -/
public initialize builtinFacetMap : IO.Ref (Option FacetConfigMap) ← IO.mkRef none
end Lake.PaperLean
