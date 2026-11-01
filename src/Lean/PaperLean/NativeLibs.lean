/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.Util.Path
import Lean.Compiler.ExternAttr
import Lean.Compiler.ExportAttr
import Lean.Compiler.InitAttr
import Lean.Compiler.IR.CompilerM
import Lean.Environment
import Init.Data.String.Legacy
import Lean.Compiler.NameMangling
import Lean.PaperLean.System
import all Lean.Compiler.MetaAttr
import all Lean.Compiler.ModPkgExt
public import Std.Data.HashMap
public import Std.Data.HashSet

-- (no `SizeOf` instances for PaperLean's types: an instance of a module of `Lean` would be one of
-- every environment that imports it, which Lean's searches would try)
set_option genSizeOf false
set_option genInjectivity false

/-!
Manifests of native libraries of packages, for `PAPERLEAN_NATIVE_LIBS`
(`src/paperlean/native_libs.cpp`): a library compiled from the `.c` files of modules is used by an
import only for imported modules whose files are those the manifest records.
-/

namespace Lean.PaperLean

/-- What a library's manifest records of a module from all of its data, its `.olean` parts (an import
may have only a module's IR). -/
public structure ModuleNativeData where
  /-- It declares `@[extern]` functions or has `builtin_initialize` declarations, or its native code
  differs from interpreting it otherwise. -/
  differs : Bool
  /-- The symbols at which the interpreter and the code of other modules can enter its `meta` code:
  those of its declarations marked `meta` (`getSymbolStem`), of their boxed versions
  (`mkMangledBoxedName`) and their `@[export]` names. -/
  metaSymbols : Array String
  /-- Its `@[export]` names. -/
  exports : Array String := #[]
  /-- The C names of its `@[extern]` declarations. -/
  externs : Array String := #[]
  /-- Why it `differs`, as far as its data tell. -/
  why : String := ""

/-- A new string object with the characters of `s` (which `"".append s` and the like need not be). -/
@[extern "lean_paperlean_copy_string"]
opaque copyString (s : @& String) : String

/--
`ModuleNativeData` of the module whose `.olean` parts (`.olean`, then `.olean.server` and
`.olean.private` if it has them) are `parts`.
-/
public def moduleNativeData (parts : Array System.FilePath) : IO ModuleNativeData := do
  let data ← readModuleDataParts parts
  let exts := #[externAttr.ext.name, builtinInitAttr.ext.name]
  -- (in `IO`, with copies of the strings of the data, and without references to the data left, so
  -- that nothing reads them after the regions are freed)
  let mut differs := false
  let mut why := ""
  let mut pkg? : Option PkgId := none
  let mut exports : Array String := #[]
  let mut externs : Array String := #[]
  for (d, _) in data do
    for (n, es) in d.entries do
      if !es.isEmpty && exts.contains n then
        differs := true
        if why.isEmpty then
          why := if n == externAttr.ext.name then "it declares `@[extern]` functions"
            else "it has `builtin_initialize` declarations"
      if n == exportAttr.ext.name then
        for e in es do
          exports := exports.push (copyString (unsafe unsafeCast e : Name × Name).2.toString)
      if n == externAttr.ext.name then
        for e in es do
          for entry in (unsafe unsafeCast e : Name × ExternAttrData).2.entries do
            if let .standard _ fn := entry then
              externs := externs.push (copyString fn)
      if n == modPkgExt.name then
        if let some e := es[0]? then
          if let some p := (unsafe unsafeCast e : Option PkgId) then
            pkg? := some (copyString p)
  let pre := mkPackageSymbolPrefix pkg?
  let mut stems : Std.HashSet String := {}
  for (d, _) in data do
    for (n, es) in d.entries do
      if n == metaExt.name then
        for e in es do
          stems := stems.insert (copyString ((unsafe unsafeCast e : Name).mangle pre))
  let mut symbols : Array String := #[]
  for (d, _) in data do
    for (n, es) in d.entries do
      if n == exportAttr.ext.name then
        for e in es do
          let (decl, exportName) := (unsafe unsafeCast e : Name × Name)
          if stems.contains (decl.mangle pre) then
            symbols := symbols.push (copyString exportName.toString)
  for s in stems do
    symbols := symbols.push s |>.push (mkMangledBoxedName s)
  let regions : Array CompactedRegion := data.map (·.2)
  for region in regions.reverse do
    unsafe region.free
  if h : externs.size > 0 then
    why := s!"it declares the `@[extern]` function {externs[0]}"
  return { differs, exports, externs, metaSymbols := symbols.qsort (· < ·), why }

/-! ### What evaluating a module's nullary constants does

Native code evaluates a nullary constant (a closed term too) once per process, its module's
initializer most of them at import, even those that nothing uses; the interpreter when it is first
used, again in each of its runs. A module may use its native code only if that makes no difference:
evaluating each of its constants has no effect and gives the same value whenever it happens.
`evalImpuritiesCore` decides this in two steps.

First, from the IR of everything that a constant can run, it rules out effects other than panics and
fatal errors. What a constant runs is what its code calls, and the closures that it creates once
something that it runs applies one (or a primitive does, such as `Thunk.get`). Compiled `IO`, `ST` and
the like take a world token, as their last parameter of type `void`, and nothing about the value given
for it tells: any value can be one through `unsafeCast`, in `unsafe` code that may be inlined into safe
code, and an `IO` action can return its token, for `initialize` to keep it, without `unsafe`. So code
that takes a token is not looked at, as what a constant holds without running it (a monad's dictionary,
a linter), and what counts is whether it can run:
- calling it directly from the code of a constant is impure, and so are `Void.mk` (`runST`, `runEST`)
  and `unsafeBaseIO`, and the primitives `dbgTrace` and the like, `sorry`, `evalConst` and `profileit`,
  which reports the time, those that
  start tasks, `Thunk.mk`, whose closure runs later, once in native code for all runs as the constant
  keeps the thunk, and, in a package's code, those that read addresses or reference counts;
- if something that a constant runs applies a closure while a closure that takes a token exists, or
  something was read from an `[init]` declaration, which may hold anything, or one of the above is
  in a closure, the flow of closures decides (`flowImpurity`): a constant is impure if a closure
  that takes a token can get all of its arguments, a value from an `[init]` declaration can be applied,
  or one of the above can run. The flow knows no types or
  tokens: a closure goes wherever a value that holds it goes, through calls, results, the fields of
  structures and primitives. An `@[extern]` of Lean's that an `@[export]` of Lean's defines is that
  code (`EvalState.forwards`), `String.Internal.foldl` for one. A primitive holds all of what it is given
  in one, and one that runs closures can apply anything that it holds, to anything that it holds, any
  number of times, and then holds what comes back too (`flowPrimitive`);
- what the flow cannot tell is impure: the application of a value of which it knows nothing, which it
  takes for code that does not run only if it can show that, and a name that modules define
  differently, whose code is not known: such a name is in none of the tables, whatever reads them, so
  that the result does not depend on the order of the modules. Evaluating a constant does not make up
  for it, as that only shows what one run does: the evaluation below is not a test for effects;
- what is found out holds for the files that were read, and for no others: a module is known to be pure
  only with the identities of its files, as they were before it was read and still were when
  it was decided (`certify`). Whoever writes a manifest compares them with the files that it records,
  and a module that it has no such verdict for is impure, so that nothing is decided by a verdict being
  absent. The imports of a module need no more than that: what it runs is in them, a module that is
  not known to be pure does not use its native code, and neither do its importers
  (`src/paperlean/native_libs.cpp`).
An `@[extern]` of a package makes its module `differs` by itself, and with it every module that
imports it.

Second, what is left is a closed computation without effects, which gives the same outcome whenever
it runs: it panics, fails or does not finish either always or never. So a panic cannot be ruled out
by looking at the code, as nearly all constants can reach one in an impossible branch of Lean's
library, but is decided by evaluating the constant once: `evalImpuritiesCore` evaluates all of them in
the interpreter, and a module one of whose constants panics, fails or takes too long is impure.
A constant that depends on an `[init]` declaration, also of Lean's, depends on its value, which may
differ from run to run, so that its evaluation decides nothing: it is impure if its own code runs anything, as anything
may panic on some value. (Not the code of the constants that it reads: these are decided on their
own, and it gets their values.) The exception is an `[init]` declaration whose value is a function
of constants alone (`initIsPure`), as those of `register_option`: then the evaluation decides as well,
with the initializers run.
-/

open IR in
/-- What a declaration does when it runs. -/
private structure DeclEffects where
  calls : Array Name := #[]
  closures : Array Name := #[]
  applies : Bool := false

open IR in
private partial def collectEffects (b : FnBody) : StateM DeclEffects Unit := do
  match b with
  | .vdecl _ _ v b =>
    match v with
    | .fap c _ => modify fun e => { e with calls := e.calls.push c }
    | .pap c _ => modify fun e => { e with closures := e.closures.push c }
    | .ap .. => modify fun e => { e with applies := true }
    | _ => pure ()
    collectEffects b
  | .jdecl _ _ v b => collectEffects v; collectEffects b
  | .case _ _ _ cs => for c in cs do collectEffects c.body
  | _ => unless b.isTerminal do collectEffects b.body

open IR in
/-- The declarations of the modules, for `evalImpuritiesCore`. -/
private structure EvalState where
  decls : Std.HashMap Name (Decl × Bool) := {}   -- with whether it is of a package
  inits : Std.HashSet Name := {}                 -- `[init]` declarations, whose value is not evaluated
  initFns : Std.HashMap Name Name := {}          -- their initializers
  forwards : Std.HashMap Name Name := {}         -- `@[extern]` declarations of Lean's that are its Lean code
  clashes : Std.HashSet Name := {}               -- names of several modules, in no other table: their code is not known

open IR in
/-- The function that the `_redArg` function `n` reduces. -/
private def dropRedArg : Name → Name
  | .str p "_redArg" => p
  | .str p s => .str (dropRedArg p) s
  | .num p i => .num (dropRedArg p) i
  | .anonymous => .anonymous

/-- Whether the last parameter of `n` is a world token (or of the function that `n` boxes). A `_redArg`
function without other parameters may have a `void` one only so that it is not a constant; it has a
token if the function that it reduces has one. -/
private def takesWorld (s : EvalState) (n : Name) : Bool :=
  let base := if n.isStr && n.getString! == "_boxed" then n.getPrefix else n
  let last (m : Name) := match s.decls[m]? with
    | some (d, _) => d.params.back?.any (·.ty matches .void)
    | none => false
  let plain := base.eraseMacroScopes
  let reduced := plain.isStr && plain.getString! == "_redArg" &&
    match s.decls[base]? with
    | some (d, _) => d.params.size == 1
    | none => false
  last base && (!reduced || last (dropRedArg base))

/-- The primitives without a world token that may run closures that they are given, also in what an
`Environment` or a `ShareCommon.StateFactory` holds. (`native_differs.sh` compares this with the
primitives that have a parameter that can hold a function, and with the C++ code that applies one.) -/
private def closureRunner (fn : String) : Bool :=
  ["lean_thunk_", "lean_task_", "lean_find_", "lean_replace_", "lean_profileit", "lean_paperlean_",
   "lean_idbg_", "lean_string_any", "lean_string_foldl", "lean_string_nextwhile", "lean_substring_all",
   "lean_substring_takewhile", "lean_add_decl", "lean_elab_add_decl", "lean_kernel_",
   "lean_mk_cases_on", "lean_state_sharecommon"].any (fn.startsWith ·)

/-- Whether the declaration is a primitive that runs closures that it is given. -/
private def runsClosures : IR.Decl → Bool
  | .extern _ _ _ ext => ext.entries.any fun
    | .standard _ fn => closureRunner fn
    | _ => false
  | _ => false

/-- Whether `c` is a closure of what reads an address or a reference count. -/
private def readsAddress (c : Name) : Bool :=
  [``ptrAddrUnsafe, ``isExclusiveUnsafe].any fun n => c == n || c == n ++ `_boxed

/-- What a value may be: a closure, by its function and how many arguments it still wants, what
a constructor made, by the declaration and variable (`varKey`) that hold it there, or anything. -/
private inductive FlowAtom where
  | closure (fn : Name) (remaining : Nat)
  | object (decl : Name) (var : Nat)
  | unknown

-- (local: an instance of a module of `Lean` would be one of every environment that imports it)
private local instance : BEq FlowAtom where
  beq
    | .closure f r, .closure g q => f == g && r == q
    | .object d x, .object e y => d == e && x == y
    | .unknown, .unknown => true
    | _, _ => false

private abbrev FlowVal := Array FlowAtom

/-- What `flowImpurity` knows: by declaration and variable (`varKey`), what values may be there, what the
fields of objects may hold, and which functions run. -/
private structure FlowState where
  vals : Std.HashMap (Name × Nat) FlowVal := {}
  fields : Std.HashMap (Name × Nat × Nat) FlowVal := {}
  /-- How many fields the objects have. -/
  sizes : Std.HashMap (Name × Nat) Nat := {}
  joins : Std.HashMap (Name × Nat) (Array IR.Param) := {}
  /-- What runs, primitives too. -/
  running : Array Name := #[]
  runningSet : Std.HashSet Name := {}
  changed : Bool := false
  bad : Option String := none

private abbrev FlowM := StateM FlowState

open IR in
/-- The index of a variable in `FlowState.vals`. The value that a function returns has index 0. -/
private def varKey (x : VarId) : Nat := x.idx + 1

private def flowAdd (key : Name × Nat) (v : FlowVal) : FlowM Unit :=
  unless v.isEmpty do
    modify fun σ =>
      let old := σ.vals[key]?.getD #[]
      let new := v.foldl (fun acc x => if acc.contains x then acc else acc.push x) old
      if new.size == old.size then σ else { σ with vals := σ.vals.insert key new, changed := true }

private def flowGet (key : Name × Nat) : FlowM FlowVal :=
  return (← get).vals[key]?.getD #[]

private def flowAddField (key : Name × Nat × Nat) (v : FlowVal) : FlowM Unit :=
  unless v.isEmpty do
    modify fun σ =>
      let old := σ.fields[key]?.getD #[]
      let new := v.foldl (fun acc x => if acc.contains x then acc else acc.push x) old
      if new.size == old.size then σ else { σ with fields := σ.fields.insert key new, changed := true }

/-- All that `v` may hold, down through fields, for what primitives do with it: closures and `unknown`. -/
private partial def flowFlatten (v : FlowVal) : FlowM FlowVal := do
  let mut out : FlowVal := #[]
  let mut seen : Array FlowAtom := #[]
  let mut todo := v
  let σ ← get
  while h : todo.size > 0 do
    let a := todo.back
    todo := todo.pop
    if seen.contains a then continue
    seen := seen.push a
    match a with
    | .object d x =>
      for i in [:σ.sizes[(d, x)]?.getD 0] do
        todo := todo ++ σ.fields[(d, x, i)]?.getD #[]
    | a => out := out.push a
  return out

open IR in
private def flowArg (f : Name) : Arg → FlowM FlowVal
  | .var x => flowGet (f, varKey x)
  | .erased => pure #[]

private def flowRun (f : Name) : FlowM Unit :=
  modify fun σ => if σ.runningSet.contains f then σ else
    { σ with running := σ.running.push f, runningSet := σ.runningSet.insert f, changed := true }

private def flowBad (why : String) : FlowM Unit :=
  modify fun σ => if σ.bad.isSome then σ else { σ with bad := some why }

open IR in
/-- Passes `args` to the parameters of `d` from the `first`-th on. -/
private def flowParams (d : Decl) (first : Nat) (args : Array FlowVal) : FlowM Unit := do
  for h : i in [:args.size] do
    if let some p := d.params[first + i]? then
      flowAdd (d.name, varKey p.x) args[i]

open IR in
/-- The result of applying what `fn` may be to `args`, in variable `res` of `f`. -/
private partial def flowApply (s : EvalState) (f : Name) (res : Nat) (fn : FlowVal) (args : Array FlowVal) :
    FlowM Unit := do
  for a in fn do
    let (t, remaining) ← match a with
      | .closure t remaining => pure (t, remaining)
      | .object .. => continue
      | .unknown =>
        flowBad "a value read from an `[init]` declaration may be applied"
        return
    let some (d, _) := s.decls[t]? | flowBad s!"`{t}` has no code"
    flowParams d (d.params.size - remaining) (args.extract 0 remaining)
    if args.size < remaining then
      flowAdd (f, res) #[.closure t (remaining - args.size)]
    else if takesWorld s t then
      flowBad s!"`{t}`, which takes a world token, may get all of its arguments"
      return
    else
      flowRun t
      match d with
      -- (a primitive has a boxed version, which is what closures are made of)
      | .extern .. => flowBad s!"the primitive `{t}` is applied without its boxed version"
      | .fdecl .. =>
        let r ← flowGet (t, 0)
        flowAdd (f, res) r
        if args.size > remaining then
          flowApply s f res r (args.extract remaining args.size)

open IR in
/-- What the primitive `d` does with `args`, in variable `res` of `f`, which holds all that it holds. If
it runs closures, it can apply each of them to as many arguments as it wants or fewer, and each argument
can be anything that it holds, also what a call before gave back, as a fold's state is; a closure that
wants more arguments is what it gets from that call. The repeated evaluation of what runs takes this to
all that the calls can give. -/
private def flowPrimitive (s : EvalState) (f : Name) (res : Nat) (d : Decl) (args : Array FlowVal) :
    FlowM Unit := do
  for a in args do flowAdd (f, res) (← flowFlatten a)
  if runsClosures d then
    let held ← flowFlatten (← flowGet (f, res))
    for c in held do
      match c with
      | .closure _ remaining =>
        for n in [min 1 remaining:remaining + 1] do
          flowApply s f res #[c] (.replicate n held)
      | c => flowApply s f res #[c] #[]

open IR in
private partial def flowBody (s : EvalState) (f : Name) (b : FnBody) : FlowM Unit := do
  match b with
  | .vdecl x _ e b =>
    let res := varKey x
    match e with
    | .ctor _ ys | .reuse _ _ _ ys =>
      flowAdd (f, res) #[.object f res]
      modify fun σ => { σ with sizes := σ.sizes.insert (f, res) ys.size }
      for h : i in [:ys.size] do
        flowAddField (f, res, i) (← flowArg f ys[i])
    | .reset _ y | .box _ y | .unbox y => flowAdd (f, res) (← flowGet (f, varKey y))
    | .proj i y =>
      for a in ← flowGet (f, varKey y) do
        match a with
        | .object d x => flowAdd (f, res) ((← get).fields[(d, x, i)]?.getD #[])
        | a => flowAdd (f, res) #[a]
    | .fap c ys =>
      let args ← ys.mapM (flowArg f)
      if ys.isEmpty && s.inits.contains c then
        flowRun c
        flowAdd (f, res) #[.unknown]
      else
        flowRun c
        match s.decls[s.forwards[c]?.getD c]? with
        | none => flowBad s!"`{c}` has no code"
        | some (d@(.fdecl ..), _) =>
          if d.params.size != args.size then
            flowBad s!"`{d.name}` does not have the parameters of `{c}`"
          flowParams d 0 args
          flowRun d.name
          flowAdd (f, res) (← flowGet (d.name, 0))
        | some (d@(.extern ..), _) => flowPrimitive s f res d args
    | .pap c ys =>
      let some (d, _) := s.decls[c]? | flowBad s!"`{c}` has no code"
      flowAdd (f, res) #[.closure c (d.params.size - ys.size)]
      flowParams d 0 (← ys.mapM (flowArg f))
    | .ap y zs => flowApply s f res (← flowGet (f, varKey y)) (← zs.mapM (flowArg f))
    | .uproj .. | .sproj .. | .lit _ | .isShared _ => pure ()
    flowBody s f b
  | .jdecl j xs v b =>
    modify fun σ => { σ with joins := σ.joins.insert (f, j.idx) xs }
    flowBody s f v
    flowBody s f b
  | .set x i y b =>
    let v ← flowArg f y
    let held ← flowGet (f, varKey x)
    for a in held do
      if let .object d o := a then flowAddField (d, o, i) v
    -- (what primitives hold is not an object here, so it holds this as well)
    if held.isEmpty || held.any (fun | .object .. => false | _ => true) then
      flowAdd (f, varKey x) v
    flowBody s f b
  | .case _ _ _ cs => for c in cs do flowBody s f c.body
  | .ret a => flowAdd (f, 0) (← flowArg f a)
  | .jmp j ys =>
    if let some xs := (← get).joins[(f, j.idx)]? then
      for y in ys, x in xs do flowAdd (f, varKey x.x) (← flowArg f y)
  | _ => unless b.isTerminal do flowBody s f b.body

open IR in
/-- Whether `b`, of `f`, applies a variable that `σ` does not know to hold a closure. A value that is
applied is one, so that this is a closure that the flow did not find, or code that does not run, which
is not for the flow to assume. -/
private partial def appliesUnknown (σ : FlowState) (f : Name) : FnBody → Bool
  | .vdecl _ _ (.ap y _) b =>
    !(σ.vals[(f, varKey y)]?.getD #[]).any (fun | .object .. => false | _ => true) ||
      appliesUnknown σ f b
  | .jdecl _ _ v b => appliesUnknown σ f v || appliesUnknown σ f b
  | .case _ _ _ cs => cs.any (appliesUnknown σ f ·.body)
  | b => !b.isTerminal && appliesUnknown σ f b.body

open IR in
/-- Why closures that take a token, values of `[init]` declarations or one of `suspects`, with why it
is one, may run in the evaluation of `root`, by the flow of closures from what it creates and reads to
what it applies, if they may or that cannot be told, or else what may run. -/
private def flowImpurity (s : EvalState) (root : Name) (suspects : Array (Name × String)) :
    Except String (Std.HashSet Name) := Id.run do
  let mut σ : FlowState := {}
  (_, σ) := (flowRun root).run σ
  repeat
    σ := { σ with changed := false }
    let mut i := 0
    while h : i < σ.running.size do
      let f := σ.running[i]
      i := i + 1
      if let some (.fdecl _ xs _ body _, _) := s.decls[f]? then
        unless xs.isEmpty && s.inits.contains f do
          (_, σ) := (flowBody s f body).run σ
      if let some why := σ.bad then return .error why
    unless σ.changed do break
  if let some (_, why) := suspects.find? (σ.runningSet.contains ·.1) then
    return .error why
  for f in σ.running do
    if let some (.fdecl _ xs _ body _, _) := s.decls[f]? then
      unless xs.isEmpty && s.inits.contains f do
        if appliesUnknown σ f body then
          return .error s!"`{f}` applies a value of which nothing is known"
  return .ok σ.runningSet

/-- What `evalImpuritiesCore` found out about a constant from its code. -/
private inductive EvalVerdict where
  /-- It has an effect, or one cannot be ruled out. -/
  | impure (why : String)
  /-- It has none, and gives the same outcome in every run. -/
  | closed
  /-- It has none, and runs no code, but holds the value of an `[init]` declaration. -/
  | readsInit (init : Name)

/-- The primitives that a constant must not reach: what they do is an effect, or depends on the process. -/
private def impurePrimitive (fn : String) : Bool :=
  fn.startsWith "lean_dbg_" || fn == "lean_void_mk" || fn == "lean_sorry" || fn == "lean_eval_const" ||
    fn == "lean_eval_check_meta" || fn == "lean_mk_thunk" || fn == "lean_profileit" ||
    ["lean_task_spawn", "lean_task_map", "lean_task_bind", "lean_paperlean_native_available",
     "lean_paperlean_native_libs_available", "lean_paperlean_foreign_code_loaded",
     "lean_paperlean_env_recording", "lean_paperlean_env_record", "lean_paperlean_env_mark_unusable"].contains fn

/-- What `failsIn` knows: by index, the variables that hold an error, the join points, and those of their
parameters that a jump gives anything else. -/
private structure FailState where
  errors : Std.HashSet Nat
  joins : Std.HashMap Nat (Array IR.Param) := {}
  notErrors : Std.HashSet Nat

open IR in
/-- Whether all that `b` returns is known to hold an error, with nothing else done on the way: it calls
nothing and changes nothing. A parameter of a join point of `b` is taken to hold one unless
`FailState.notErrors` has it. (A jump gives nothing for the object that is not reused.) -/
private partial def failsIn : FnBody → StateM FailState Bool
  | .vdecl x _ e b => do
    match e with
    | .fap .. | .pap .. | .ap .. => return false
    | .ctor i _ | .reuse _ i _ _ =>
      if i.name != ``EST.Out.error then return false
      modify fun σ => { σ with errors := σ.errors.insert x.idx }
    | _ => pure ()
    failsIn b
  | .jdecl j xs v b => do
    modify fun σ => { σ with
      joins := σ.joins.insert j.idx xs
      errors := xs.foldl (init := σ.errors) fun acc p =>
        if σ.notErrors.contains p.x.idx then acc else acc.insert p.x.idx }
    return (← failsIn v) && (← failsIn b)
  | .case _ _ _ cs => do
    for c in cs do
      unless ← failsIn c.body do return false
    return true
  | .jmp j ys => do
    let σ ← get
    let some xs := σ.joins[j.idx]? | return false
    for y in ys, x in xs do
      if let .var z := y then
        unless σ.errors.contains z.idx do
          modify fun σ => { σ with notErrors := σ.notErrors.insert x.x.idx }
    return true
  | .ret (.var x) => return (← get).errors.contains x.idx
  | .unreachable => return true
  | .inc (b := b) .. | .dec (b := b) .. | .del (b := b) .. => failsIn b
  | _ => return false

open IR in
/-- Whether the alternative `b` of a `case` on `x`, an `EST.Out` that holds an error, can only give an
error. What is taken of the parameters of join points is checked until the jumps agree with it. -/
private partial def onlyFails (x : VarId) (b : FnBody) (notErrors : Std.HashSet Nat := {}) : Bool :=
  let (ok, σ) := (failsIn b).run { errors := ({} : Std.HashSet Nat).insert x.idx, notErrors }
  ok && (σ.notErrors.size == notErrors.size || onlyFails x b σ.notErrors)

open IR in
/-- Whether the expression reads one of the variables. -/
private def readsAny (xs : Std.HashSet Nat) : IR.Expr → Bool
  | .ctor _ ys | .fap _ ys | .pap _ ys => ys.any (argIn xs)
  | .reuse x _ _ ys | .ap x ys => xs.contains x.idx || ys.any (argIn xs)
  | .reset _ x | .proj _ x | .uproj _ x | .sproj _ _ x | .box _ x | .unbox x | .isShared x => xs.contains x.idx
  | .lit _ => false
where
  argIn (xs : Std.HashSet Nat) : Arg → Bool
    | .var x => xs.contains x.idx
    | .erased => false

open IR in
/-- The alternatives of a `case` on an `EST.Out`, for `ok` and for `error`, if it has just these: an
alternative of another type is about other tags. -/
private def outAlternatives (cs : Array Alt) : Option (FnBody × FnBody) :=
  let named (n : Name) := cs.findSome? fun
    | .ctor i b => if i.name == n then some b else none
    | _ => none
  let other := cs.findSome? fun
    | .default b => some b
    | _ => none
  if cs.size != 2 then none else
    match named ``EST.Out.ok, named ``EST.Out.error, other with
    | some ok, some error, none | some ok, none, some error | none, some error, some ok => some (ok, error)
    | _, _, _ => none

open IR in
/-- Whether what code with a world token gives, which `pending` has until a `case` tells `ok` from `error`,
cannot get into anything but the result of `b`, of a function that has a token if `world` is set, and of
what is dropped. It may only be returned, for the caller to do the same, or be told apart, and an `error`
can only give an error. Past `ok`, it is as if nothing had happened. -/
private partial def outcomesEnd (s : EvalState) (world : Bool) (pending : Std.HashSet Nat) : FnBody → Bool
  | .vdecl x _ e b =>
    !readsAny pending e &&
      match e with
      | .fap c _ =>
        if takesWorld s c then world && outcomesEnd s world (pending.insert x.idx) b
        else outcomesEnd s world pending b
      | _ => outcomesEnd s world pending b
  | .jdecl _ _ v b => outcomesEnd s world pending v && outcomesEnd s world pending b
  | .case _ x _ cs =>
    if pending.contains x.idx then
      match outAlternatives cs with
      | some (ok, error) => onlyFails x error && outcomesEnd s world (pending.erase x.idx) ok
      | none => false
    else cs.all (outcomesEnd s world pending ·.body)
  | .jmp _ ys => !ys.any fun
    | .var x => pending.contains x.idx
    | .erased => false
  | .set x _ y b =>
    !pending.contains x.idx &&
      (match y with
       | .var y => !pending.contains y.idx
       | .erased => true) && outcomesEnd s world pending b
  | .uset x _ y b => !pending.contains x.idx && !pending.contains y.idx && outcomesEnd s world pending b
  | .sset x _ _ y _ b => !pending.contains x.idx && !pending.contains y.idx && outcomesEnd s world pending b
  | .setTag x _ b => !pending.contains x.idx && outcomesEnd s world pending b
  | b => b.isTerminal || outcomesEnd s world pending b.body

open IR in
/-- Whether the value of the `[init]` declaration `i` is the same in every run that gives it one: its
initializer applies no closure, reads no other `[init]` declaration and calls no primitive that takes a
world token, except `registerOption`, which gives `Unit` or an error, as earlier imports decide. That is
all that can differ, and `outcomesEnd` shows that a value cannot depend on it. -/
private partial def initIsPure (s : EvalState) (i : Name) : Bool := Id.run do
  let some fn := s.initFns[i]? | return false
  if fn.isAnonymous then return false
  let mut seen : Std.HashSet Name := {}
  let mut todo := #[fn]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if s.inits.contains n then return false
    let some (d, packaged) := s.decls[n]? | return false
    if n == ``registerOption && !packaged then continue
    match d with
    | .extern _ xs _ ext =>
      if xs.back?.any (·.ty matches .void) then return false
      for e in ext.entries do
        match e with
        | .standard _ fn => if impurePrimitive fn || closureRunner fn then return false
        | .opaque => return false
        | _ => pure ()
      if let some t := s.forwards[n]? then todo := todo.push t
    | .fdecl _ _ _ body _ =>
      let e := ((collectEffects body).run {}).2
      if e.applies || !outcomesEnd s (takesWorld s n) {} body then return false
      if packaged && (e.calls.contains ``ptrAddrUnsafe || e.calls.contains ``isExclusiveUnsafe) then
        return false
      todo := todo ++ e.calls
  return true

open IR in
/-- What the code of the nullary declaration `root` allows. The state holds the effects of the
declarations seen so far. -/
private def evalImpurity (s : EvalState) (root : Name) :
    StateM (Std.HashMap Name DeclEffects) EvalVerdict := do
  -- what it runs, and whether as part of evaluating another constant that it reads, which is decided
  -- on its own as to panics: what it gives is a value; and whether it is known only to be in a closure
  let mut seen : Std.HashSet (Name × Bool) := {}
  let mut todo := #[(root, false, false)]
  let mut closures : Array Name := #[]
  let mut suspects : Array (Name × String) := #[]
  let mut applies := false
  let mut runsCode := false
  let mut worldClosure? : Option Name := none
  let mut inits : Array Name := #[]
  let mut initsInClosures : Array Name := #[]
  repeat
    while h : todo.size > 0 do
      let (n, nested, inClosure) := todo.back
      todo := todo.pop
      if seen.contains (n, nested) then continue
      seen := seen.insert (n, nested)
      if !nested && n != root then runsCode := true
      if s.clashes.contains n then
        return .impure s!"`{root}` runs `{n}`, which modules define differently"
      if n.getRoot == `unsafeBaseIO then
        if inClosure then
          suspects := suspects.push (n, s!"`{root}` may run `unsafeBaseIO`")
          continue
        return .impure s!"`{root}` runs `unsafeBaseIO`"
      if takesWorld s n then
        if inClosure then
          suspects := suspects.push (n, s!"`{root}` may run `{n}`, which takes a world token")
          continue
        return .impure s!"`{root}` runs `{n}`, which takes a world token"
      if s.inits.contains n && (s.decls[n]?.any fun (d, _) => d.params.isEmpty) then
        if inClosure then initsInClosures := initsInClosures.push n else inits := inits.push n
        continue
      let some (d, packaged) := s.decls[n]? | return .impure s!"`{root}` runs `{n}`, which has no code"
      match d with
      | .extern _ _ _ ext =>
        for e in ext.entries do
          match e with
          | .standard _ fn =>
            if impurePrimitive fn then
              if inClosure then
                suspects := suspects.push (n, s!"`{root}` may run `{n}`")
              else
                return .impure s!"`{root}` runs `{n}`"
            if closureRunner fn then
              applies := true
          | .opaque => return .impure s!"`{root}` runs `{n}`, which has no code"
          | _ => pure ()
        if let some t := s.forwards[n]? then
          todo := todo.push (t, nested, inClosure)
      | .fdecl _ _ _ body _ =>
        let e ← match (← get)[n]? with
          | some e => pure e
          | none =>
            let e := ((collectEffects body).run {}).2
            modify (·.insert n e)
            pure e
        if packaged && (e.calls.contains ``ptrAddrUnsafe || e.calls.contains ``isExclusiveUnsafe) then
          if inClosure then
            suspects := suspects.push (n, s!"`{root}` may read an address or a reference count in `{n}`")
          else
            return .impure s!"`{root}` reads an address or a reference count in `{n}`"
        applies := applies || e.applies
        for c in e.calls do
          let constant := match s.decls[c]? with
            | some (.fdecl _ ys _ _ _, _) => ys.isEmpty
            | _ => false
          todo := todo.push (c, nested || constant, inClosure)
        for c in e.closures do
          if packaged && readsAddress c then
            suspects := suspects.push (c, s!"`{root}` may read an address or a reference count through `{c}`")
          if takesWorld s c then worldClosure? := some c else closures := closures.push c
    unless applies && !closures.isEmpty do break
    -- (run by the application, whatever constant holds them)
    todo := closures.map (·, false, true)
    closures := #[]
  if applies && (worldClosure?.isSome || !inits.isEmpty || !initsInClosures.isEmpty || !suspects.isEmpty) then
    match flowImpurity s root suspects with
    | .error why => return .impure s!"evaluating `{root}`: {why}"
    | .ok running => inits := inits ++ initsInClosures.filter running.contains
  if let some i := inits.find? (!initIsPure s ·) then
    if runsCode then
      return .impure s!"what `{root}` runs depends on the `[init]` declaration `{i}`"
    return .readsInit i
  return .closed

/-- The files that are read of the module of the `.olean` file `olean`, whether it has them or not, in
the order of `module_file_kind` (`paperlean/olean_pack.h`). -/
public def moduleFiles (olean : System.FilePath) : Array System.FilePath :=
  #[olean, olean.addExtension "server", olean.addExtension "private", olean.withExtension "ir.sig",
    olean.withExtension "ir"]

/-- An identity (`fileIdentity`) as text. -/
public def identityText (id : ByteArray) : String :=
  id.foldl (init := "") fun s b => (s.push (Nat.digitChar (b.toNat / 16))).push (Nat.digitChar (b.toNat % 16))

/-- The text for a file that does not exist, in place of its identity. -/
public def noFile : String := "-"

/-- The identities of `moduleFiles`. -/
public def moduleIdentities (olean : System.FilePath) : BaseIO (Array String) :=
  (moduleFiles olean).mapM fun f => return ((← fileIdentity f.toString).map identityText).getD noFile

open IR in
/-- What `readModuleDataParts` gives of a module, for `evalImpuritiesCore`: its imports, IR, `[init]`
declarations and `@[export]` names, with the identities of its files from before it was read. -/
private structure EvalModule where
  file : System.FilePath
  packaged : Bool
  imports : Array Name
  decls : Array Decl
  inits : Array (Name × Name)
  exports : Array (Name × Name)
  identities : Array String

/-- The `.olean` parts of `olean` that exist. -/
private def oleanParts (olean : System.FilePath) : IO (Array System.FilePath) :=
  return #[olean] ++ (← #[olean.addExtension "server", olean.addExtension "private"].filterM (·.pathExists))

open IR in
-- (the regions stay mapped: names and code of the modules are used until the end, and the process
-- that does this ends then)
private unsafe def readEvalModule (olean : System.FilePath) (packaged : Bool) : IO EvalModule := do
  let identities ← moduleIdentities olean
  let data ← readModuleDataParts (← oleanParts olean)
  let ir := olean.withExtension "ir"
  let irData ← if ← ir.pathExists then readModuleDataParts #[olean.withExtension "ir.sig", ir] else pure #[]
  let mut decls : Array Decl := #[]
  let mut inits : Array (Name × Name) := #[]
  let mut exports : Array (Name × Name) := #[]
  for (d, _) in data ++ irData do
    for (n, es) in d.entries do
      if n == regularInitAttr.ext.name || n == builtinInitAttr.ext.name then
        for e in es do
          inits := inits.push (unsafeCast e : Name × Name)
      if n == exportAttr.ext.name then
        for e in es do
          exports := exports.push (unsafeCast e : Name × Name)
  -- the IR: of the `.ir` file (whose first part only has signatures), or of the `.olean` file
  if let some (d, _) := (if irData.isEmpty then data[0]? else irData.back?) then
    for (n, es) in d.entries do
      if n == declMapExt.name then
        decls := decls ++ (unsafeCast es : Array Decl)
  let some (main, _) := data[0]? | throw <| IO.userError s!"cannot read {olean}"
  return { file := olean, packaged, imports := main.imports.map (·.module), decls, inits, exports, identities }

/-- The number of panics so far, whatever was done about their messages. -/
@[extern "lean_paperlean_panic_count"]
private opaque panicCount : BaseIO USize

/-- What `evalImpuritiesCore` tells about its progress: a line per event, for the process that runs it. -/
public abbrev EvalLog := String → IO Unit

/-- What is known about modules, by the `.olean` files that they are found by. -/
public structure EvalVerdicts where
  /-- The modules that are not pure, with the reason. -/
  impure : Array (System.FilePath × String) := #[]
  /-- The modules that are pure as long as their files have these identities (`moduleIdentities`).
  One that neither has is not known to be pure. -/
  certified : Std.HashMap System.FilePath (Array String) := {}

/-- `v` with what a line of `EvalLog` says. -/
public def EvalVerdicts.add (v : EvalVerdicts) (line : String) : EvalVerdicts :=
  match line.splitOn "\t" with
  | "ok" :: f :: ids => { v with certified := v.certified.insert (f : System.FilePath) ids.toArray }
  | "impure" :: f :: why => { v with impure := v.impure.push ((f : System.FilePath), "\t".intercalate why) }
  | _ => v

/-- Tells that the module of `file`, which was read with the identities `ids`, is pure, unless the
files are no longer those, whatever it was that happened to read them. -/
private def certify (log : EvalLog) (file : System.FilePath) (ids : Array String) : IO Unit := do
  if (← moduleIdentities file) == ids then
    log s!"ok\t{file}\t{"\t".intercalate ids.toList}"
  else
    log s!"impure\t{file}\tits files changed while it was analysed"

/-- Evaluates the constants `constants` of each module, in one environment if they can be imported
together, in the order of their imports, as a module's constants evaluate those that they use. -/
private unsafe def evalConstants (modules : Array (Name × System.FilePath × Array Name × Array String))
    (log : EvalLog) : IO Unit := do
  enableInitializersExecution
  match ← (importModules (modules.map fun (m, _) => { module := m }) {} (leakEnv := true) (loadExts := true)).toBaseIO with
  | .error e =>
    if modules.size ≤ 1 then
      for (_, f, _) in modules do
        log s!"impure\t{f}\tit cannot be imported: {(toString e).replace "\n" " "}"
      return
    -- (modules that are never imported together can define the same declarations)
    let half := modules.size / 2
    evalConstants modules[:half] log
    evalConstants modules[half:] log
  | .ok env =>
    let order : Std.HashMap Name Nat := env.header.moduleNames.foldl (init := {}) fun m n => m.insert n m.size
    let sorted := modules.qsort fun a b => (order[a.1]?.getD 0) < (order[b.1]?.getD 0)
    for (_, file, constants, ids) in sorted do
      log s!"start\t{file}"
      let before ← panicCount
      let mut why? : Option String := none
      for c in constants do
        match env.evalConst Unit {} c (checkMeta := false) with
        | .error e => why? := some s!"evaluating `{c}` fails: {e}"
        | .ok _ =>
          if (← panicCount) != before then
            why? := some s!"`{c}` panics"
        if why?.isSome then break
      if let some why := why? then
        log s!"impure\t{file}\t{why}"
      else
        certify log file ids

/--
Tells of the modules of the `.olean` files of packages `modules`, each with its name, whether evaluating
a nullary constant may depend on when or how often that happens, with the reason, or else that they
are pure, except for those of `decided`, which are only read. What they import is found in the search
path `sp`; below `toolchain` is Lean's own code. Constants of `modules` are evaluated, which needs them
in `searchPathRef`.
-/
private unsafe def evalImpuritiesCore (modules : Array (Name × System.FilePath)) (sp : SearchPath)
    (toolchain : System.FilePath) (decided : Std.HashSet System.FilePath) (log : EvalLog) : IO Unit := do
  let isOwn (f : System.FilePath) := f.toString.startsWith (toolchain.toString ++ "/")
  let mut loaded : Array EvalModule := #[]
  let mut seen : Std.HashSet Name := modules.foldl (fun s m => s.insert m.1) {}
  let mut seenFiles : Std.HashSet System.FilePath := modules.foldl (fun s m => s.insert m.2) {}
  let mut frontier := modules.map (·.2)
  -- (the code of a primitive of Lean's can be in a module that the packages do not import)
  for m in [`Init, `Std, `Lean] do
    unless seen.contains m do
      seen := seen.insert m
      if let some f ← sp.findWithExt "olean" m then
        unless seenFiles.contains f do
          seenFiles := seenFiles.insert f
          frontier := frontier.push f
  while !frontier.isEmpty do
    let tasks ← frontier.mapM fun f => IO.asTask (readEvalModule f (!isOwn f))
    let mut next : Array System.FilePath := #[]
    for t in tasks do
      -- (a file that cannot be read has no code, which the constants that run it are told by)
      let .ok m := t.get | continue
      loaded := loaded.push m
      for i in m.imports do
        unless seen.contains i do
          seen := seen.insert i
          if let some f ← sp.findWithExt "olean" i then
            unless seenFiles.contains f do
              seenFiles := seenFiles.insert f
              next := next.push f
    frontier := next
  let mut decls : Std.HashMap Name (IR.Decl × Bool) := Std.HashMap.emptyWithCapacity (loaded.foldl (· + ·.decls.size) 0)
  let mut inits : Std.HashSet Name := {}
  let mut initFns : Std.HashMap Name Name := {}
  -- (first, as nothing may be decided by the code of the module that happens to be read last)
  let mut owners : Std.HashMap Name System.FilePath := {}
  let mut clashes : Std.HashSet Name := {}
  for m in loaded do
    for n in m.decls.map (·.name) ++ m.inits.map (·.1) do
      match owners[n]? with
      | some f => if f != m.file then clashes := clashes.insert n
      | none => owners := owners.insert n m.file
  for m in loaded do
    for d in m.decls do
      unless clashes.contains d.name do
        decls := decls.insert d.name (d, m.packaged)
    for (d, fn) in m.inits do
      unless clashes.contains d do
        inits := inits.insert d
        initFns := initFns.insert d fn
  let mut exported : Std.HashMap String Name := {}
  for m in loaded do
    unless m.packaged do
      for (d, e) in m.exports do
        exported := exported.insert e.toString d
  let mut forwards : Std.HashMap Name Name := {}
  for m in loaded do
    unless m.packaged do
      for d in m.decls do
        if let .extern _ _ _ ext := d then
          for e in ext.entries do
            if let .standard _ fn := e then
              if let some t := exported[fn]? then
                if t != d.name && !clashes.contains d.name then forwards := forwards.insert d.name t
  let s : EvalState := { decls, inits, initFns, forwards, clashes }
  decls := {}
  let names : Std.HashMap System.FilePath Name := modules.foldl (fun m (n, f) => m.insert f n) {}
  let mut effects : Std.HashMap Name DeclEffects := {}
  -- (one that was not read has not been decided)
  for (_, f) in modules do
    unless decided.contains f || loaded.any (·.file == f) do
      log s!"impure\t{f}\tit cannot be read"
  let mut toEvaluate : Array (Name × System.FilePath × Array Name × Array String) := #[]
  let mut constants := 0
  for m in loaded do
    let some name := names[m.file]? | continue
    if decided.contains m.file then continue
    let mut why? : Option String := none
    let mut closed : Array Name := #[]
    for d in m.decls do
      if d.params.isEmpty && (s.clashes.contains d.name || !d.isExtern && !s.inits.contains d.name) then
        let (verdict, effects') := (evalImpurity s d.name).run effects
        effects := effects'
        match verdict with
        | .impure why => why? := some why
        | .closed => closed := closed.push d.name
        | .readsInit _ => pure ()
        if why?.isSome then break
    if let some why := why? then
      log s!"impure\t{m.file}\t{why}"
    else if closed.isEmpty then
      certify log m.file m.identities
    else
      toEvaluate := toEvaluate.push (name, m.file, closed, m.identities)
      constants := constants + closed.size
  log s!"static\t{loaded.size}\t{constants}\t{s.clashes.size}"
  evalConstants toEvaluate log

/-- `evalImpuritiesCore`, which `log` is told the verdicts of. -/
@[implemented_by evalImpuritiesCore]
public opaque evalImpuritiesSafe (modules : Array (Name × System.FilePath)) (sp : SearchPath)
    (toolchain : System.FilePath) (decided : Std.HashSet System.FilePath) (log : EvalLog) : IO Unit

/--
The main program of the process that `paperlean prepare` runs `evalImpuritiesCore` in (it maps
everything that it reads): `modulesFile` has a line `<name>\t<.olean file>\t<0 or 1>` for each module, 1
for those decided already, and the events are appended to `eventsFile`, with `done` as the last one. A
module whose constants do not finish in `seconds`, or need more than `mebibytes` of address space
(`limitAddressSpace`), ends the process, which then has started but not finished it. The standard
output names a module that it has been waiting for.
-/
public def evalImpuritiesMain (modulesFile eventsFile : System.FilePath) (seconds mebibytes : Nat) : IO Unit := do
  -- (of this `lean`: the one in the `PATH` is official Lean's under the front end)
  let toolchain ← getLibDir (← getBuildDir)
  let lines ← IO.FS.lines modulesFile
  let fields := lines.map (·.splitOn "\t")
  let modules := fields.filterMap fun
    | [n, f, _] => some (n.toName, (f : System.FilePath))
    | _ => none
  let decided : Std.HashSet System.FilePath := fields.foldl (init := {}) fun s l =>
    match l with
    | [_, f, "1"] => s.insert f
    | _ => s
  let events ← IO.FS.Handle.mk eventsFile .append
  let startedAt ← IO.mkRef (none : Option (Nat × String))
  let log (line : String) : IO Unit := do
    events.putStrLn line
    events.flush
    let now ← IO.monoMsNow
    match line.splitOn "\t" with
    | ["start", f] =>
      startedAt.set (some (now, f))
      limitAddressSpace (mebibytes * 1048576).toUSize
    | _ =>
      startedAt.set none
      limitAddressSpace 0
  let _ ← IO.asTask (prio := .dedicated) do
    let mut told := ""
    repeat
      IO.sleep 1000
      if let some (t, f) ← startedAt.get then
        let waited := (← IO.monoMsNow) - t
        if waited > seconds * 1000 then
          IO.Process.exit 3
        if waited ≥ 2000 && f != told then
          told := f
          let name := (modules.find? (·.2.toString == f)).elim f (toString ·.1)
          IO.println s!"  waiting for the constants of {name} (at most {seconds} s)"
          (← IO.getStdout).flush
  discard <| evalImpuritiesSafe modules (← searchPathRef.get) toolchain decided log
  log "done"
  -- (not waiting for the task above)
  IO.Process.exit 0

/-- The names that the `.c` file `c` (`EmitC.lean`) defines, and those that it declares without
defining them. -/
@[extern "lean_paperlean_c_symbols"]
public opaque cSymbols (c : @& String) : IO (Array String × Array String)

/-- Those of `names` that neither the libraries `libs` (with those they are linked against), nor
`lean.h`, nor what this process is linked against define. -/
@[extern "lean_paperlean_undefined_symbols"]
public opaque undefinedSymbols (names libs : @& Array String) : IO (Array String)

/-- Why Lean cannot load the library `lib`, or `""` if it can: it binds all symbols when it loads a
library. -/
@[extern "lean_paperlean_load_error"]
public opaque loadError (lib : @& String) : IO String

/-- A module of a native library, for its manifest. -/
public structure NativeManifestModule where
  name : Name
  /-- The `.c` file compiled into the library. -/
  cFile : String
  /-- The paths of its files, which must be those the `.c` file was generated with, in the order
  `.olean`, `.olean.server`, `.olean.private`, `.ir.sig`, `.ir` (empty for a file the module does not
  have). -/
  files : Array String
  /-- `moduleNativeData` of its `.olean` parts. -/
  data : ModuleNativeData

/--
Writes to `out` the manifest of the native library `lib`, linked against the libraries of the
manifests `deps`, and compiled from `modules`. Other modules' code is entered at the symbols
`extSymbols` (the `metaSymbols` of other libraries' modules) or those of `modules`, as far as the
manifest records. Returns, per module, why it found that its native code is not to be used, if it did.
-/
@[extern "lean_paperlean_write_native_manifest"]
public opaque writeNativeManifestFiles (out lib : @& String) (deps : @& Array String)
    (modules : @& Array NativeManifestModule) (extSymbols : @& Array String) : IO (Array String)

end Lean.PaperLean
