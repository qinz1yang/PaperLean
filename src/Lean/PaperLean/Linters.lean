/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
import Lean.Linter.ConstructorAsVariable
import Lean.Linter.UnusedVariables

-- (no `SizeOf` instances for PaperLean's types: an instance of a module of `Lean` would be one of
-- every environment that imports it, which Lean's searches would try)
set_option genSizeOf false
set_option genInjectivity false

/-!
Faster versions of two of Lean's linters, which replace them in `lintersRef` under their names and
report the same messages. Lean's own definitions stay as they are, so that the code compiled from
them is official Lean's.
- `linter.constructorNameAsVariable` takes the type of a binder from its local declaration,
  instantiates its metavariables without `runMetaM`, and runs `whnf` only where it could change the
  head of the type; it finds the constructors of each inductive type once.
- `linter.unusedVariables` walks the info trees of a command once to find the macro expansions of
  all of its candidate variables, not once per candidate (`collectMacroExpansions?`).
-/

namespace Lean.PaperLean.Linters
open Lean Elab Command Linter UnusedVariables

/-- For each type constant seen that is an inductive type: its constructors that have 0 fields, with
the last components of their names. Pattern variables can't be confused with constructors that want
arguments. -/
private abbrev NullaryCtors := Std.HashMap Name (Option (Array (String × Name)))

/-- The constructors of the inductive type `tn` that have 0 fields (`NullaryCtors`), if it is
one. -/
private def nullaryCtorsOf? (cache : IO.Ref NullaryCtors) (tn : Name) :
    CommandElabM (Option (Array (String × Name))) := do
  if let some cs? := (← cache.get)[tn]? then
    return cs?
  let mut cs? := none
  if let some (.inductInfo i) := (← getEnv).find? tn then
    let mut cs := #[]
    for c in i.ctors do
      if let some (.ctorInfo ctorInfo) := (← getEnv).find? c then
        if ctorInfo.numFields > 0 then continue
      if let .str _ cn := c then
        cs := cs.push (cn, c)
    cs? := some cs
  cache.modify (·.insert tn cs?)
  return cs?

/-- The type of the binder `ti` of `ldecl` after `instantiateMVars` and `whnf` in `runMetaM`, up to
`mdata`. -/
private def binderTypeWhnf (cache : IO.Ref NullaryCtors) (ci : ContextInfo) (ti : TermInfo)
    (ldecl : LocalDecl) : CommandElabM Expr := do
  -- (`inferType` of the variable is the type of `ldecl`)
  let ty := ti.expectedType?.getD ldecl.type
  -- (`instantiateMVars` in `runMetaM`, whose metavariable context is `ci.mctx`)
  let ty := if ty.hasMVar then (instantiateMVarsCore ci.mctx ty).1 else ty
  -- (`whnf` leaves a type without metavariables as it is, up to `mdata`, if it is a pi, a sort, or
  -- an application of an inductive type or of a local variable without a value)
  let whnfFixed ← match ty.getAppFn' with
    | .const tn _ => Option.isSome <$> nullaryCtorsOf? cache tn
    | .fvar x => pure (ti.lctx.find? x matches some (.cdecl ..))
    | _ => pure (ty.isForall || ty.isSort)
  if !ty.hasMVar && whnfFixed then
    return ty
  ti.runMetaM ci (Meta.whnf ty)

/-- `Lean.Linter.constructorNameAsVariable`, which computes the types of binders without `runMetaM`
where `whnf` keeps them, and the constructors of each inductive type once. -/
private def constructorNameAsVariable : Linter where
  name := ``Lean.Linter.constructorNameAsVariable
  run cmdStx := do
    unless getLinterValue linter.constructorNameAsVariable (← getLinterOptions) do
      return
    let some cmdStxRange := cmdStx.getRange?
      | return

    let infoTrees := (← get).infoState.trees.toArray
    let warnings : IO.Ref (Std.HashMap Lean.Syntax.Range (Syntax × Name × Name)) ← IO.mkRef {}
    let constRanges : IO.Ref (Std.HashSet Lean.Syntax.Range) ← IO.mkRef {}
    let nullaryCtors : IO.Ref NullaryCtors ← IO.mkRef {}

    for tree in infoTrees do
      tree.visitM' (postNode := fun ci info _ => do
        match info with
        | .ofTermInfo ti =>
          match ti.expr with
          | .fvar id .. =>
            let some range := info.range? | return
            if (← warnings.get).contains range then return
            let .original .. := info.stx.getHeadInfo | return
            if ti.isBinder then
              -- This is a local variable declaration.
              let some ldecl := ti.lctx.find? id | return
              -- Skip declarations which are outside the command syntax range, like `variable`s
              -- (it would be confusing to lint these), or those which are macro-generated
              if !cmdStxRange.contains range.start || ldecl.userName.hasMacroScopes then return
              let opts ← ci.options.toLinterOptions
              -- we have to check for the option again here because it can be set locally
              if !getLinterValue linter.constructorNameAsVariable opts then return
              if let n@(.str .anonymous s) := info.stx.getId then
                -- Check whether the type is an inductive type, and get its constructors
                let ty ← binderTypeWhnf nullaryCtors ci ti ldecl
                if let .const tn _ := ty.getAppFn' then
                  if let some cs := ← nullaryCtorsOf? nullaryCtors tn then
                    for (cn, c) in cs do
                      if cn == s then
                        warnings.modify (·.insert range (info.stx, n, c))
            else pure ()
          | .const .. =>
            let some range := info.range? | return
            let .original .. := info.stx.getHeadInfo | return
            if ti.isBinder then
              constRanges.modify fun s => s.insert range
          | _ => pure ()
        | _ => pure ())

    -- Sort the outputs by position, excluding those that are also defining global constants.
    -- Global constants occur for example in `structure` fields
    for (range, declStx, userName, ctorName) in (← warnings.get).toArray.qsort (·.1.start < ·.1.start) do
      unless (← constRanges.get).contains range do
        logLint linter.constructorNameAsVariable declStx <|
          m!"Local variable '{userName}' resembles constructor '{ctorName}' - " ++
          m!"write '.{userName}' (with a dot) or '{ctorName}' to use the constructor."

/--
The nodes of info trees that `collectMacroExpansions?` visits (`InfoTree.visitM`), in pre-order,
for `macroExpansionsIn?`: each one's range, its macro expansion if it is one, its parent's index
plus one (0 for none), and the end of its subtree.
-/
private structure ExpansionNodes where
  ranges : Array (Option Syntax.Range) := #[]
  expansions : Array (Option Elab.MacroExpansionInfo) := #[]
  parents : Array Nat := #[]
  ends : Array Nat := #[]
  /-- Whether `collectMacroExpansions?` panics on a tree pushed since this was last reset, at a node
  or a partial context without a context around it. -/
  irregular : Bool := false

/-- Pushes the nodes of `tree`, a child of the node `parent` (plus one), under a context if
`hasCtx`. -/
private partial def ExpansionNodes.push (nodes : ExpansionNodes) (hasCtx : Bool) (parent : Nat)
    (tree : Elab.InfoTree) : ExpansionNodes :=
  match tree with
  | .context ci t =>
    if hasCtx || ci matches .commandCtx _ then nodes.push true parent t
    else { nodes with irregular := true }
  | .node i cs =>
    if !hasCtx then { nodes with irregular := true } else
    let n := nodes.ranges.size
    let { ranges, expansions, parents, ends, irregular } := nodes
    let expansion? := if let .ofMacroExpansionInfo e := i then some e else none
    let nodes := ExpansionNodes.mk (ranges.push i.range?) (expansions.push expansion?)
      (parents.push parent) (ends.push 0) irregular
    let { ranges, expansions, parents, ends, irregular } := cs.foldl (·.push true (n + 1)) nodes
    ExpansionNodes.mk ranges expansions parents (ends.set! n ranges.size) irregular
  | .hole _ => nodes

/--
`collectMacroExpansions? range` of the tree whose nodes are `nodes[start:stop]`: the macro
expansions among the node where it ends and that node's ancestors, from the bottom up. It goes down
into the first child with a node in its subtree that contains `range` as long as there is one: to
the first node that contains `range`, then the first in that node's subtree, and so on.
-/
private def macroExpansionsIn? (nodes : ExpansionNodes) (start stop : Nat) (range : Syntax.Range) :
    Option (List Elab.MacroExpansionInfo) := Id.run do
  let mut found := none
  let mut bound := stop
  for i in [start:stop] do
    if i ≥ bound then break
    if nodes.ranges[i]!.any fun r => r.contains range.start && r.contains range.stop true then
      found := some i
      bound := nodes.ends[i]!
  let some i := found | return none
  let mut i := i
  let mut expansions := #[]
  for _ in [start:stop] do
    if let some e := nodes.expansions[i]! then
      expansions := expansions.push e
    let p := nodes.parents[i]!
    if p == 0 then break
    i := p - 1
  return some expansions.toList

/-- Lean's `hasSorry` of `Lean.Linter.UnusedVariables`, which is private. -/
private def hasSorry (stx : Syntax) : Bool :=
  stx.find? (fun
    -- `@[unused_variables_ignore_fn]` can be used to extend this list
    | `(sorry) | `(tactic| sorry) | `(tactic| admit) => true
    | _ => false) |>.isSome

/-- `Lean.Linter.UnusedVariables.unusedVariables`, which finds the macro expansions of all of the
candidate variables of a command with one walk of its info trees. -/
private def unusedVariables : Linter where
  name := ``Lean.Linter.UnusedVariables.unusedVariables
  run cmdStx := do
    unless getLinterUnusedVariables (← getLinterOptions) do
      return

    -- NOTE: `messages` is local to the current command
    if (← get).messages.hasErrors then
      return

    let some cmdStxRange := cmdStx.getRange?
      | return

    -- We used to look for `sorry` on the `Expr` level, which is more robust, but just too expensive
    -- on huge declarations (see e.g. `omega_stress` benchmark).
    if hasSorry cmdStx then
      return

    let infoTrees := (← get).infoState.trees.toArray

    let linterSets := (linterSetsExt.getState (← getEnv)).merged

    -- Run the main collection pass, resulting in `s : References`.
    let (_, s) ← (collectReferences infoTrees cmdStxRange linterSets).run {}

    -- If there are no local defs then there is nothing to do
    if s.fvarDefs.isEmpty then return

    -- Resolve all recursive references in `fvarAliases`.
    -- At this point everything in `fvarAliases` is guaranteed not to be itself an alias,
    -- and should point to some element of `FVarDefinition.aliases` in `s.fvarDefs`
    let fvarAliases : Std.HashMap FVarId FVarId := s.fvarAliases.fold (init := {}) fun m id baseId =>
      m.insert id (followAliases s.fvarAliases baseId)

    let getCanonVar (id : FVarId) : FVarId := fvarAliases.getD id id

    -- Collect all non-alias fvars corresponding to `fvarUses` by resolving aliases in the list.
    -- Unlike `s.fvarUses`, `fvarUsesRef` is guaranteed to contain no aliases.
    let fvarUsesRef ← IO.mkRef <| fvarAliases.fold (init := s.fvarUses) fun fvarUses id baseId =>
      if fvarUses.contains id then fvarUses.insert baseId else fvarUses

    -- Collect ignore functions
    let ignoreFns ← getUnusedVariablesIgnoreFns

    let mut initializedMVars := false
    let mut expansionNodes : ExpansionNodes := {}
    -- (where the nodes of each tree pushed so far start and end, unless it is irregular)
    let mut treeNodes : Array (Option (Nat × Nat)) := #[]
    let mut unused := #[]
    -- For each variable definition, check to see if it is used
    for (range, { userName, stx := declStx, opts, aliases }) in s.fvarDefs.toArray do
      let fvarUses ← fvarUsesRef.get
      -- If any of the `fvar`s corresponding to this declaration is (an alias of) a variable in
      -- `fvarUses`, then it is used
      if aliases.any fun id => fvarUses.contains (getCanonVar id) then continue
      -- If this is a global declaration then it is (potentially) used after the command
      if s.constDecls.contains range then continue

      -- Get the syntax stack for this variable declaration
      let some ((id', _) :: stack) := cmdStx.findStack? (·.getRange?.any (·.includes range))
        | continue

      -- If it is blacklisted by an `ignoreFn` then skip it
      let linterOpts ← opts.toLinterOptions
      if id'.isIdent && ignoreFns.any (· declStx stack linterOpts) then continue

      -- Evaluate ignore functions again on macro expansion outputs
      -- (`collectMacroExpansions? range` of each tree, which visits the trees only once in all)
      let mut ignored := false
      for t in [0:infoTrees.size] do
        if t == treeNodes.size then
          let start := expansionNodes.ranges.size
          expansionNodes := expansionNodes.push false 0 infoTrees[t]!
          treeNodes := treeNodes.push <|
            if expansionNodes.irregular then none else some (start, expansionNodes.ranges.size)
          expansionNodes := { expansionNodes with irregular := false }
        let macroExpansions? ← match treeNodes[t]! with
          | some (start, stop) => pure (macroExpansionsIn? expansionNodes start stop range)
          | none => collectMacroExpansions? range infoTrees[t]!
        let some macroExpansions := macroExpansions? | continue
        if macroExpansions.any fun expansion =>
          -- in a macro expansion, there may be multiple leafs whose (synthetic) range
          -- includes `range`, so accept strict matches only
          if let some (_ :: stack) :=
            expansion.output.findStack?
              (·.getRange?.any (·.includes range))
              (fun stx => stx.isIdent && stx.getRange?.any (· == range))
          then
            ignoreFns.any (· declStx stack linterOpts)
          else
            false
        then
          ignored := true
          break
      if ignored then
        continue

      -- Visiting the metavariable assignments is expensive so we delay initialization
      if !initializedMVars then
        -- collect additional `fvarUses` from tactic assignments
        visitAssignments (← IO.mkRef {}) fvarUsesRef s.assignments
        -- Resolve potential aliases again to preserve `fvarUsesRef` invariant
        fvarUsesRef.modify fun fvarUses => fvarUses.toArray.map getCanonVar |> .insertMany {}
        initializedMVars := true
        let fvarUses ← fvarUsesRef.get
        -- Redo the initial check because `fvarUses` could be bigger now
        if aliases.any fun id => fvarUses.contains (getCanonVar id) then continue

      -- If we made it this far then the variable is unused and not ignored
      unused := unused.push (declStx, userName)

    -- Sort the outputs by position
    for (declStx, userName) in unused.qsort (·.1.getPos?.get! < ·.1.getPos?.get!) do
      let suggestion : Meta.Hint.Suggestion := s!"_{userName}"
      let suggestion := { suggestion with span? := declStx, diffGranularity := .none }
      let hint ← liftCoreM <| MessageData.hint
        m!"The binding can be removed (if unused) or named `_` (if used implicitly). \
          Alternatively, prefix the name with `_` to silence this warning:" #[suggestion]
      logLint linter.unusedVariables declStx
        (m!"Variable name `{userName}` is not explicitly referenced." ++ hint)

-- (after Lean's linters, which the imports register)
builtin_initialize lintersRef.modify fun ls => ls.map fun l =>
  if l.name == ``Lean.Linter.constructorNameAsVariable then constructorNameAsVariable
  else if l.name == ``Lean.Linter.UnusedVariables.unusedVariables then unusedVariables
  else l

end Lean.PaperLean.Linters
