/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Init.Prelude

public section

/-!
A comparison of object graphs for testing that two computations produce exactly the same objects,
used by `PAPERLEAN_IMPORT=check`.
-/

namespace Lean.PaperLean

/--
The first difference between the object graphs reachable from `a` and `b`, if any; this is the
comparison behind `PAPERLEAN_IMPORT=check`. Objects outside the heap (in compacted regions, e.g.
loaded `.olean` files) must be the same objects; heap objects must correspond one to one, so that
sharing agrees as well, and have the same contents, array capacities included if `strict`; if not
`strict`, empty arrays outside the heap (closed terms of different modules) are not told apart.
-/
@[extern "lean_paperlean_graph_diff"]
unsafe opaque graphDiff {α : Type} (a b : @& α) (strict : Bool) : Option String

end Lean.PaperLean
