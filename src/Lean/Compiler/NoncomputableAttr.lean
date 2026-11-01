/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.EnvExtension

public section

namespace Lean

-- `sync` as it's written to from both main branch and codegen branch
builtin_initialize noncomputableExt : TagDeclarationExtension ← mkTagDeclarationExtension (asyncMode := .sync)

/-- Mark in the environment extension that the given declaration has been declared by the user as `noncomputable`. -/
def addNoncomputable (env : Environment) (declName : Name) : Environment :=
  noncomputableExt.tag env declName

/--
PaperLean: `noncomputableExt.isTagged (asyncMode := .sync) env declName`, which waits for every
earlier environment branch (e.g. every earlier proof and kernel check), but read in mode `.local`
for a declaration of this module that is a theorem or not declared yet (the kind is the private
constant's, known without waiting). Such a declaration is tagged by the branch that declares it
and the branches it was started from (`elabMutualDef`, `addNonRec`), and by another branch only if
its name is given to a `compileDecls` that fails there (a theorem's only with other names, as the
compiler skips propositions), which is an error unless the caller passed `logErrors := false`. So
this reads the same tags without waiting but in that case.
-/
private def isNoncomputableSync (env : Environment) (declName : Name) (_ : Unit) : Bool :=
  if (env.getModuleIdxFor? declName).isNone &&
      ((env.setExporting false).findAsync? declName).all (·.kind matches .thm) then
    noncomputableExt.isTagged (asyncMode := .local) env declName
  else
    noncomputableExt.isTagged (asyncMode := .sync) env declName

/--
Returns `true` when the given declaration is tagged `noncomputable`.
-/
-- PaperLean: (not inlined: its body calls PaperLean's code)
@[noinline] def isNoncomputable (env : Environment) (declName : Name) (asyncMode := noncomputableExt.toEnvExtension.asyncMode) : Bool :=
  -- PaperLean: without waiting where possible (`isNoncomputableSync`), not while recording
  -- environment accesses (`Lean.PaperLean.EnvDeps`), which then record Lean's read
  if asyncMode matches .sync && PaperLean.nativeAvailable env && !PaperLean.envRecording env then
    PaperLean.uncounted isNoncomputableSync env declName ()
  else
  noncomputableExt.isTagged (asyncMode := asyncMode) env declName

end Lean
-- Modified by PaperLean.
