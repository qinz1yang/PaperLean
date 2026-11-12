/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.Environment

public section

/-!
The entry point of `Lean.PaperLean.QuotedSyntax` for `evalSyntaxConstant` (`Lean.Elab.Util`) and the
delaborator. It imports only what those modules' imports already bring, so that PaperLean adds
nothing to their import closures but its own modules; `Lean.PaperLean.QuotedSyntax`, which needs more
of Lean, installs itself here when it is initialized (in Lean's own executables and plugins). Where it
is not, the hook answers `none` and the caller evaluates the constant as before.
-/

namespace Lean.PaperLean.QuotedSyntax

/-- The decoder of `Lean.PaperLean.QuotedSyntax` once it is initialized; otherwise `none` for every
constant. -/
builtin_initialize ofConstantRef : IO.Ref (Environment → Name → Option Syntax) ← IO.mkRef fun _ _ => none

/-- The `Syntax` value of the quoted tactic constant `constName` of this module without evaluating it,
if `Lean.PaperLean.QuotedSyntax` is initialized and the constant is one it reads; `none` otherwise. -/
unsafe def ofConstant? (env : Environment) (constName : Name) : Option Syntax :=
  (unsafeBaseIO ofConstantRef.get) env constName

end Lean.PaperLean.QuotedSyntax
