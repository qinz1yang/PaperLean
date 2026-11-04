/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Std
import Lean
import Lake.All

/-!
The code of Lean's own modules that other modules compile into theirs: the LCNF bodies (base and
mono phase) that an importer may inline under some `compiler.small` (an inline attribute, or a body
that is neither `@[noinline]` nor recursive) or specializes (a parameter whose specialization info
causes specialization).
Following them from the declarations that code can name (not internal, not of a PaperLean module)
through the constants they refer to and through `implemented_by`, this prints every reachable
reference to a constant of a PaperLean module or to a function implemented by `lean_paperlean_…`
C code: code that PaperLean compiles from such a body would call what official Lean does not have.
(Upstream functions whose bodies call PaperLean's code are therefore `@[noinline]`.)
(This file is not a `module`, so it sees the bodies of all declarations, of which `module`s see
those of exported ones.)
-/

open Lean Compiler LCNF

def isPaperLeanModule (m : Name) : Bool :=
  (`Lean.PaperLean).isPrefixOf m || (`Lake.PaperLean).isPrefixOf m

def isUsable (env : Environment) (base : Bool) (decl : Decl .pure) : Bool :=
  match decl.value with
  | .extern .. => false
  | .code _ =>
    (match decl.inlineAttr? with
     | some .inline | some .alwaysInline | some .inlineIfReduce | some .macroInline => true
     | some .noinline => false
     -- (inlined if at most `compiler.small` in size, which may be any number)
     | none => !decl.recursive) ||
      base && (getSpecEntryCore? env decl.name).any (·.paramsInfo.any (·.causesSpecialization))

partial def refs (c : Code .pure) (acc : Array Name) : Array Name :=
  match c with
  | .let d k => refs k (match d.value with | .const n .. => acc.push n | _ => acc)
  | .fun d k _ | .jp d k => refs k (refs d.value acc)
  | .cases cs => cs.alts.foldl (fun acc alt => refs alt.getCode acc) acc
  | _ => acc

/-- Why code calling `n` calls what official Lean does not have, if it does. -/
def problem? (env : Environment) (n : Name) : Option String := do
  if let some idx := env.getModuleIdxFor? n then
    if let some m := env.header.moduleNames[idx]? then
      if isPaperLeanModule m then
        return s!"a declaration of {m}"
  if let some d := getExternAttrData? env n then
    for e in d.entries do
      if let .standard _ s := e then
        if s.startsWith "lean_paperlean" then
          return s!"implemented by {s}"
  none

#eval show CoreM Unit from do
  let env ← getEnv
  let decl? (base : Bool) (n : Name) := getDeclCore? env (if base then baseExt else monoExt) n
  let mut stack : Array (Bool × Name × List Name) := #[]
  for h : idx in 0...env.header.moduleNames.size do
    if isPaperLeanModule env.header.moduleNames[idx] then
      continue
    for base in [true, false] do
      for decl in (if base then baseExt else monoExt).getModuleEntries env idx do
        if !decl.name.isInternal && isUsable env base decl then
          stack := stack.push (base, decl.name, [decl.name])
  let mut seen : Std.HashSet (Bool × Name) := {}
  let mut found : Std.HashMap Name (String × List Name) := {}
  while h : stack.size > 0 do
    let (base, n, path) := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains (base, n) then
      continue
    seen := seen.insert (base, n)
    let some decl := decl? base n | continue
    let .code c := decl.value | continue
    for r in refs c #[] do
      for r in [r] ++ (getImplementedBy? env r).toList do
        if let some why := problem? env r then
          unless found.contains r do
            found := found.insert r (why, r :: path)
          continue
        if let some d := decl? base r then
          if isUsable env base d then
            stack := stack.push (base, r, r :: path)
  for (r, why, path) in found.toArray.qsort (·.1.toString < ·.1.toString) do
    IO.println s!"{r}: {why}, reached from {" <- ".intercalate (path.map toString)}"

/-!
The calling conventions (parameter types and borrowed parameters, result type, in the IR and in the
impure LCNF signature) of the upstream functions whose compiled code PaperLean changes or that it
makes `@[noinline]` (some of them private), and of their `_redArg` and `_boxed` versions, which code
compiled by PaperLean calls: the expected ones are official Lean's, which also shows that official
Lean has them.
-/

def changedUpstream : List Name := [
  `Lake.compileLeanModule, `Lake.download, `Lake.tar, `Lake.fetchFileHash,
  `Lake.Module.cacheOutputHashes, `Lake.Workspace.runBuild, `Lake.loadWorkspace,
  `Lean.isNoncomputable, `Lean.Elab.Command.runTermElabM, `Lean.Elab.runFrontend,
  `Lean.Language.Lean.process, `Lean.Language.Lean.processCommands,
  `Lean.Elab.Term.runTactic, `Lean.EnvExtension.modifyState, `Lean.EnvExtension.setState,
  `Lean.EnvExtension.getState, `Lean.Environment.AddConstAsyncResult.commitConst,
  `Lean.Environment.addConstAsync, `Lean.Environment.containsOnBranch,
  `Lean.Environment.enableRealizationsForConst, `Lean.Environment.find?,
  `Lean.Environment.findAsync?, `Lean.Environment.findConstVal?, `Lean.Environment.findTask,
  `Lean.TagDeclarationExtension.isTagged, `Lean.getReducibilityStatusCore,
  `Lean.Environment.getLocalConstantInfos, `Lean.Environment.realizeValue,
  `Lean.Environment.toKernelEnv, `Lean.finalizeImport, `Lean.importModules, `Lean.mkModuleData,
  `Lean.KeyedDeclsAttribute.getEntries, `Lean.KeyedDeclsAttribute.addBuiltin, `Lean.Meta.isProofQuick, `Lean.Meta.synthInstance,
  `Lean.Meta.synthInstanceCore?, `Lean.ResolveName.resolveGlobalName,
  `Lean.ResolveName.resolveNamespace, `Lean.resolveNamespace, `Lean.ScopedEnvExtension.addImportedFn,
  `Lean.ScopedEnvExtension.getState, `Lean.Server.dedupReferences,
  `Lean.Server.getModuleContainingDecl?, `Lean.instFromJsonModuleArtifacts.fromJson,
  `Lean.instToJsonModuleArtifacts.toJson, `Lean.instToJsonModuleSetup.toJson,
  `Lean.Expr.instantiateLevelParams, `Lean.SearchPath.findWithExt, `Lean.findLean, `Lean.findOLean,
  `Lean.moduleNameOfFileName, `Lean.Meta.realizeValue, `Lean.IR.findEnvDecl,
  `Lean.Meta.SynthInstance.getInstances, `Lean.Environment.realizeConst, `Lean.Compiler.LCNF.main,
  `Lean.instFromJsonModuleSetup.fromJson, `Lean.Environment.evalConst, `Lean.Meta.inferTypeImp,
  `Lean.Meta.whnfImp, `Lean.Elab.expandMacroImpl?, `Lean.Elab.toAttributeKind,
  `Lean.Elab.Term.elabWithDeclName, `Lean.ModuleSetup.load, `Lean.Meta.getFunInfo,
  `Lean.Meta.getFunInfoNArgs, `Lean.registerScopedEnvExtensionUnsafe,
  `Lake.Module.inputFacetConfig, `Lake.Module.leanArtsFacetConfig]

def changedUpstreamPrivate : List Name := [
  mkPrivateNameCore `Lake.Build.Module `Lake.Module.buildLean,
  mkPrivateNameCore `Lake.Build.Module `Lake.Module.recBuildLean,
  mkPrivateNameCore `Lake.Build.Module `Lake.Module.recFetchInput,
  mkPrivateNameCore `Lake.CLI.Main `Lake.lakeCli,
  mkPrivateNameCore `Lean.Environment `Lean.EnvExtension.getStateUnsafe,
  mkPrivateNameCore `Lean.Meta.FunInfo `Lean.Meta.getFunInfoAux,
  mkPrivateNameCore `Lake.Build.Library `Lake.LeanLib.recCollectLocalModules,
  mkPrivateNameCore `Lean.Meta.SynthInstance `Lean.Meta.cacheResult,
  mkPrivateNameCore `Lean.Meta.WHNF `Lean.Meta.cache,
  mkPrivateNameCore `Lean.Elab.Term.TermElabM `Lean.Elab.Term.elabUsingElabFnsAux,
  mkPrivateNameCore `Lean.Environment `Lean.finalizePersistentExtensions,
  mkPrivateNameCore `Lean.Environment `Lean.Environment.modifyCheckedAsync,
  mkPrivateNameCore `Lake.CLI.Main `Lake.lake]

#eval show CoreM Unit from do
  let env ← getEnv
  for n in changedUpstream ++ changedUpstreamPrivate do
    for n in [n, n.str "_redArg", n.str "_boxed", (n.str "_redArg").str "_boxed"] do
      if let some d := IR.findEnvDecl env n then
        let ps := d.params.toList.map fun p => (if p.borrow then "@& " else "") ++ toString p.ty
        IO.println s!"{n}: {" ".intercalate ps} : {d.resultType}"
      if let some s := getSigCore? env impureSigExt n then
        let ps := s.params.toList.map fun p => (if p.borrow then "@& " else "") ++ toString p.type
        IO.println s!"{n} (impure): {" ".intercalate ps} : {s.type}"
