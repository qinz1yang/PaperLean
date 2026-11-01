# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that what these files observe after a reuse is what they observe after Lean's own elaboration
# (not the contents of Lean's caches, which may lack entries that Lean adds): each file gives what
# PaperLean gives when it reuses nothing (`PAPERLEAN_EXACT`), which is what official
# Lean 4.35.0-rc3 gives (also with `-DmaxHeartbeats=0 -DmaxRecDepth=0`; the checks of "does not test
# what it should" say what that is). Section variables, which PaperLean reuses across commands
# (`Lean.PaperLean.SectionVars`), with macros and elaborators that read the current namespace or the
# quotation context of the declaration, the name generator after the variables, Lean's own reads of the
# namespace (`with_decl_name% ?`), and the binder names with macro scopes of the declarations that
# use reused variables (`HygNames`); a macro, or a helper that a macro calls, replaced under the same
# name after the environment was restored; and the entries of Lean's `inferType` cache after a reuse
# whose variables have names of the declaration's quotation context, each checked against `inferType`
# without the cache (`CacheProbe`). Typeclass results, which PaperLean reuses across commands
# (`Lean.PaperLean.TCCache`): an elaborator reports the name generator and the metavariable counter
# after reused searches, also after code whose fresh names depend on the entries that the searches
# put in Lean's caches, and after reused searches whose lookups of pure keys found other entries; the
# files reuse results (`PAPERLEAN_REUSE_STATS`). The oracle (`PAPERLEAN_REUSE_ORACLE`), which compares
# each reuse of a typeclass result and its effects with Lean's search, finds no difference. Where the
# output shows nothing, the `.olean`, `.ilean` and `.c` are those of a run that reuses nothing: after
# searches recorded before or after the realizations of a constant were enabled, whose names reach the
# `_closed_` declarations of the compiler, with tactics and Verso docstrings that depend on the identifiers
# of section variables, and with literals above 2^63, whose objects a reuse takes from an earlier command. A builtin registered at run time, which is outside what PaperLean supports,
# stops with an error that names it and points to `lake build`.

export PAPERLEAN_REUSE=1
cd "$TMP_DIR"
header='import Lean.Elab.ElabRules
open Lean Elab Term'

# In Lean, `h` is `` `B = `A `` in `B`, so `t2` does not typecheck.
cat > NsMacro.lean <<EOF
$header
macro "curNs%" : term => do return quote (← Macro.getCurrNamespace)
variable (h : curNs% = \`A)
include h
namespace A
theorem t1 : (\`A : Name) = \`A := h
end A
namespace B
theorem t2 : (\`A : Name) = \`A := h
end B
EOF
cat > ByElab.lean <<EOF
$header
variable (h : by_elab do
  return mkApp3 (mkConst \`\`Eq [1]) (mkConst \`\`Name) (toExpr (← getCurrNamespace)) (toExpr \`A))
include h
namespace A
theorem t1 : (\`A : Name) = \`A := h
end A
namespace B
theorem t2 : (\`A : Name) = \`A := h
end B
EOF
cat > NsElab.lean <<EOF
$header
elab "curNsE%" : term => return toExpr (← getCurrNamespace)
variable (h : curNsE% = \`A)
include h
namespace A
theorem t1 : (\`A : Name) = \`A := h
end A
namespace B
theorem t2 : (\`A : Name) = \`A := h
end B
EOF
# The same through Lean's own `do` elaborator, which runs the code of another attribute.
cat > NsDoElem.lean <<'EOF'
import Lean
open Lean Elab Do
set_option backward.do.legacy false
syntax (name := curNsDo) "curNsDo%" : doElem
@[doElem_elab curNsDo] def elabCurNsDo : DoElab := fun _ dec => do
  elabDoElem (← `(doElem| return $(quote (← getCurrNamespace)):term)) dec
@[doElem_control_info curNsDo] def infoCurNsDo : ControlInfoHandler := fun _ =>
  return { numRegularExits := 0, returnsEarly := true }
variable (h : (Id.run do curNsDo%) = `A)
include h
namespace A
theorem t1 : (`A : Name) = `A := h
end A
namespace B
theorem t2 : (`A : Name) = `A := h
end B
EOF
# Lean's own: in Lean, `h` is `` `B.foo = `A.foo `` in `B`, so `t2` does not typecheck, and `t3`
# does.
cat > NsDeclName.lean <<EOF
$header
variable (h : with_decl_name% ?foo decl_name% = \`A.foo)
include h
namespace A
theorem t1 : (\`A.foo : Name) = \`A.foo := h
end A
namespace B
theorem t2 : (\`A.foo : Name) = \`A.foo := h
theorem t3 : (\`B.foo : Name) = \`A.foo := h
end B
EOF
# In Lean, `h` differs in each declaration.
cat > QuotCtx.lean <<EOF
$header
macro "ctx%" : term => do return quote (← MonadQuotation.getContext)
variable (n : Name) (h : n = ctx%)
include h
theorem t1 : True := by trace_state; trivial
theorem t2 : True := by trace_state; trivial
EOF
# The name generator after the variables, in a later elaborator: in Lean, `t2`'s statement is
# `294 = 290`, which does not typecheck.
cat > NgenAfter.lean <<EOF
$header
elab "ngen%" : term => return mkNatLit (← getNGen).idx
variable {α : Type} (a b : α) (h : a = b)
include h
theorem t1 : ngen% = ngen% := rfl
theorem t2 : ngen% = 290 := rfl
EOF
# The name generator after reused typeclass searches (`t2` repeats `t1`'s problems, and so on),
# also after Lean's code that may find the entries that the searches put in its caches (`t5`, `t6`)
# and with section variables (`t7` to `t10`).
cat > TcNgen.lean <<'EOF'
import Lean.Elab.ElabRules
open Lean Elab Term Meta
elab "ngen%" : term => do
  logInfo m!"ngen {(← getNGen).idx}, mvars {(← getMCtx).mvarCounter}"
  return mkNatLit 0
class C (α : Type) where c : Nat
class D (α : Type) extends C α where d : Nat
instance : C Nat := ⟨1⟩
instance : D Nat := { c := 1, d := 2 }
instance [C α] : C (List α) := ⟨2⟩
instance [D α] : D (List α) := { c := 2, d := 3 }
instance [C α] [C β] : C (α × β) := ⟨3⟩
instance {α β : Type} [C β] : C (α → β) := ⟨4⟩
def f (n : Nat) : Nat := n + 1
theorem t1 : C.c (List (List Nat)) + D.d (List Nat) = C.c (List (List Nat)) + D.d (List Nat) ∧
    ngen% = 0 := ⟨rfl, rfl⟩
theorem t2 : C.c (List (List Nat)) + D.d (List Nat) = C.c (List (List Nat)) + D.d (List Nat) ∧
    ngen% = 0 := ⟨rfl, rfl⟩
theorem t3 : C.c (Nat → List Nat) + C.c (Nat × List Nat) = 7 ∧ ngen% = 0 := ⟨rfl, rfl⟩
theorem t4 : C.c (Nat → List Nat) + C.c (Nat × List Nat) = 7 ∧ ngen% = 0 := ⟨rfl, rfl⟩
theorem t5 : C.c (Nat → List Nat) = 4 ∧ (fun x => f x) 1 = f 1 ∧ ngen% = 0 := ⟨rfl, rfl, rfl⟩
theorem t6 : C.c (Nat → List Nat) = 4 ∧ (fun x => f x) 1 = f 1 ∧ ngen% = 0 := ⟨rfl, rfl, rfl⟩
section
variable {α : Type} [D α] (x : α)
theorem t7 : C.c (List α) + D.d (List (List α)) = C.c (List α) + D.d (List (List α)) ∧
    ngen% = 0 := ⟨rfl, rfl⟩
theorem t8 : C.c (List α) + D.d (List (List α)) = C.c (List α) + D.d (List (List α)) ∧
    ngen% = 0 := ⟨rfl, rfl⟩
theorem t9 : C.c (α → List α) + C.c (List α × α) = C.c (α → List α) + C.c (List α × α) ∧
    ngen% = 0 := ⟨rfl, rfl⟩
theorem t10 : C.c (α → List α) + C.c (List α × α) = C.c (α → List α) + C.c (List α × α) ∧
    ngen% = 0 := ⟨rfl, rfl⟩
end
#eval show MetaM Unit from do logInfo m!"end ngen {(← getNGen).idx}"
EOF
# The name generator after typeclass searches whose lookups of `funInfo` of imported constants find
# other entries than when they were recorded (the problem of `Nat` after that of `Int`, and alone),
# which are reused, and a theorem that Lean rejects.
cat > TcPure.lean <<'EOF'
import Lean.Elab.ElabRules
open Lean Elab Term Meta
elab "ngen%" : term => do
  logInfo m!"ngen {(← getNGen).idx}, mvars {(← getMCtx).mvarCounter}"
  return mkNatLit 0
theorem t1 : (default : List Int) = [] ∧ (default : List Nat) = [] ∧ ngen% = 0 := ⟨rfl, rfl, rfl⟩
theorem t2 : (default : List Nat) = [] ∧ ngen% = 0 := ⟨rfl, rfl⟩
theorem t3 : (default : List Bool) = [] ∧ ngen% = 0 := ⟨rfl, rfl⟩
theorem t4 : (default : List Int) = [] ∧ (default : List Bool) = [] ∧ ngen% = 0 := ⟨rfl, rfl, rfl⟩
example : (default : List Nat) = [1] := rfl
#eval show MetaM Unit from do logInfo m!"end ngen {(← getNGen).idx}"
EOF

# user code that reads only universe names and syntax
cat > Transparent.lean <<EOF
$header
partial def freshLevelName (used : List Name) : Name :=
  go 1
where
  go (n : Nat) : Name :=
    let u := (\`u).appendIndexAfter n
    if used.contains u then go (n + 1) else u
elab "Typ*" : term => do
  let levelNames ← getLevelNames
  let u := freshLevelName levelNames
  setLevelNames (u :: levelNames)
  return .sort (.succ (mkLevelParam u))
notation "ℕ'" => Nat
variable {α : Typ*} (a : α) (n : ℕ')
include a n
theorem t1 : True := trivial
theorem t2 : True := trivial
#check @t2
EOF

# the binder names, with macro scopes of each declaration's quotation context, of declarations that
# use reused variables
cat > HygNames.lean <<'EOF'
import Lean.Elab.Command
open Lean Elab Command
class C (α : Type) where c : α
notation "Fn" α => ∀ (_ : α), α
variable {α : Type} [C α] (f : α → α) (g : Fn α) [Inhabited α]
include f g
theorem t1 : f = f := rfl
theorem t2 : g = g := rfl
def t3 : α := f (g default)
partial def names (e : Expr) : List Name := match e with
  | .forallE n t b _ | .lam n t b _ => n :: names t ++ names b
  | _ => []
#eval show CommandElabM Unit from do
  for n in [``t1, ``t2, ``t3] do
    let some ci := (← getEnv).find? n | return
    logInfo m!"{n}: {repr (names ci.type)}"
EOF

# a macro, and a helper that a macro calls, replaced under the same names after the environment
# was restored (in Lean, `h` is `1 = 0` in `B`)
for v in Macro Helper; do
  if [ $v = Macro ]; then
    first='"@[macro curNs] def nsMacro : Macro := fun _ => pure (Syntax.mkNumLit \"0\")",'
    second='"@[macro curNs] def nsMacro : Macro := fun _ => do return Syntax.mkNumLit (if (← Macro.getCurrNamespace) == `B then \"1\" else \"0\")",'
  else
    first='"def pick : MacroM Syntax := pure (Syntax.mkNumLit \"0\")", "@[macro curNs] def nsMacro : Macro := fun _ => pick",'
    second='"def pick : MacroM Syntax := do return Syntax.mkNumLit (if (← Macro.getCurrNamespace) == `B then \"1\" else \"0\")", "@[macro curNs] def nsMacro : Macro := fun _ => pick",'
  fi
  cat > Restored$v.lean <<EOF
import Lean
open Lean Elab Command
syntax (name := curNs) "curNs%" : term
def runCommands (ss : List String) : CommandElabM Unit := do
  for s in ss do
    let .ok stx := Parser.runParserCategory (← getEnv) \`command s | throwError "parse failure"
    elabCommand stx
run_cmd do
  let env ← getEnv
  runCommands [$first
    "section", "variable (h : curNs% = (0 : Nat))", "include h",
    "theorem pre0 : (0 : Nat) = 0 := h", "theorem pre1 : (0 : Nat) = 0 := h", "end"]
  setEnv env
  runCommands [$second
    "variable (h : curNs% = (0 : Nat))", "include h", "namespace A",
    "theorem t0 : (0 : Nat) = 0 := h", "theorem t1 : (0 : Nat) = 0 := h", "end A",
    "namespace B", "theorem t2 : (0 : Nat) = 0 := h", "end B"]
EOF
done
# the entries of Lean's `inferType` cache after the variables are reused (in Lean, each entry is
# what `inferType` computes without the cache)
cat > CacheProbe.lean <<'EOF'
import Lean
open Lean Elab Term Meta Command
elab "probe" : command => runTermElabM fun _ => do
  let cache := (← getThe Meta.State).cache.inferType
  let mut bad : Nat := 0
  for (k,v) in cache do
    let fresh ← (show MetaM Expr from
      withReader (fun ctx => { ctx with cacheInferType := false }) (inferType k.expr))
    unless v.equal fresh do
      bad := bad + 1
      logInfo m!"wrong cached value: {repr v}\nrecomputed: {repr fresh}"
  logInfo m!"wrong entries: {bad}"
set_option quotPrecheck false in
notation "Fn" => ∀ (_ : Nat), Nat
variable (f : Fn) (h : (fun (_ : Nat) => f) 0 = f)
probe
probe
EOF

# a macro that does not read the namespace, whose variables are reused in another one
cat > CrossNsMacro.lean <<EOF
$header
notation "ℕ'" => Nat
variable (n : ℕ') (l : List Nat) (t : Type)
theorem t1 : n = n := rfl
namespace A
theorem t2 : n = n := rfl
end A
EOF
# variables in other namespaces (`T` is the same constant in `A`, `B` and `B.C`), with Lean's own
# elaborators, whose declarations a file that imports `Lean` has
cat > CrossNs.lean <<'EOF'
import Lean
def T := Nat
variable (n : T) (l : List T) (U : Type)
theorem t1 : n = n := rfl
namespace A
theorem t2 : n = n := rfl
end A
namespace B
theorem t3 : n = n := rfl
end B
theorem B.C.t3 : n = n := rfl
#check @B.C.t3
EOF

# searches inside an `isDefEq`, here of the instance of `A.y` when a search unifies `A.y ?inst + 0`, which
# may empty the caches of that `isDefEq` and leave entries there, as the oracle compares. This one finds a
# result, after which `assignOutParams` empties them for a reuse too.
cat > TcInDefEq.lean <<'EOF'
set_option maxSynthPendingDepth 3
class A (α : Type) where
  x : Nat
  y : Nat
instance : A Nat := ⟨1, 2⟩
class S (α : Type) (n : Nat) where
instance {α : Type} [A α] : S α (A.y α + 0) := ⟨⟩
def useS (α : Type) (n : Nat) [S α n] : Nat := n
theorem t1 : useS Nat (2 + 0) = 2 := rfl
theorem t2 : useS Nat (2 + 0) = 2 := rfl
theorem t3 : useS Nat (2 + 0) = 2 := rfl
EOF
# ... this one finds nothing: the instance of `A (Fin 3)` is tried, which empties the caches and leaves
# what it compared there, and the `isDefEq` of the first instance of `S` goes on with these
cat > TcEmptied.lean <<'EOF'
abbrev F (β : Type) (_ : Nat) : Type := β
structure T (p : Prop) where
class A (α : Type) where
  y : Nat
instance : A (Fin (2 + 0)) := ⟨2⟩
class S (α β : Type) where
  x : Nat
instance {α : Type} [A α] : S α (F (T (∀ n : Nat, (fun x => x) n = n)) (A.y α + 0)) := ⟨0⟩
instance (priority := low) {α β : Type} : S α β := ⟨1⟩
def useS (α β : Type) [S α β] : Nat := S.x α β
theorem t1 : useS (Fin 3) (F (T (∀ n : Nat, n = n)) (1 + 0)) = 1 := rfl
theorem t2 : useS (Fin 3) (F (T (∀ n : Nat, n = n)) (3 + 0)) = 1 := rfl
theorem t3 : useS (Fin 3) (F (T (∀ n : Nat, n = n)) (3 + 0)) = 1 := rfl
theorem t4 : useS (Fin 3) (F (T (∀ n : Nat, n = n)) (5 + 0)) = 1 := rfl
EOF
# ... and this one has no instance to try: no `isDefEq` runs, and the caches stay as they are
grep -v '^instance : A (Fin (2 + 0))' TcEmptied.lean > TcLeft.lean
# ... and this one leaves entries that hold a binder name with macro scopes of its problem, which a
# reuse in another command, with another such name, must not put back: the search of the local instance
# unifies the binder of `Ty%`, then fails at `Never`. (Reads the cache only to say what is in it.)
cat > TcPermNames.lean <<'EOF'
module
public import Lean
import all Lean.Meta.Basic
open Lean Meta Elab Command Term
set_option linter.unusedVariables false
class Never : Prop where
  no : False
structure T (p : Prop) where
class A (α : Type) where
macro "Ty%" x:term : term => `(T (∀ n : Nat, n = $x))
meta partial def bnames (e : Expr) : List Name := match e with
  | .forallE n t b _ | .lam n t b _ => n :: bnames t ++ bnames b
  | .app f a => bnames f ++ bnames a
  | .mdata _ b => bnames b
  | _ => []
elab "probe " t:term : command => liftTermElabM do
  let ty ← elabType t
  forallTelescope ty fun _ ty => do
    discard <| synthInstance? ty
    let names := (bnames ty).filter Name.hasMacroScopes
    let mut bad : Nat := 0
    for (k,_) in (← getThe Meta.State).cache.defEqPerm.toList do
      let ns := (bnames k.lhs ++ bnames k.rhs).filter Name.hasMacroScopes
      if ns.any (fun n => !names.contains n) then bad := bad + 1
    logInfo m!"stale keys {bad}"
probe ∀ (x : Nat) [inst : ∀ [h : Never], A (T (∀ n : Nat, (fun y => y) n = x))], A (Ty% x)
probe ∀ (x : Nat) [inst : ∀ [h : Never], A (T (∀ n : Nat, (fun y => y) n = x))], A (Ty% x)
EOF
# a search in `grind`'s theorem instantiation, whose name generator starts again each time
cat > TcInGrind.lean <<'EOF'
universe u
class D (α : Type u) where d : α → Prop
structure B (α : Type u) where
  val : α
instance {α : Type u} [D α] : D (B α) := ⟨fun x => D.d x.val⟩
instance : D Nat := ⟨fun _ => True⟩
theorem d_all {α : Type u} [D α] [Inhabited α] (a : α) (h : D.d a) : D.d (B.mk a) := h
grind_pattern d_all => B.mk a
set_option linter.defProp false
def e1 (a : Nat) (h : D.d a) : D.d (B.mk a) := by grind
def e2 (a : Nat) (h : D.d a) : D.d (B.mk a) := by grind
EOF

# searches recorded before `enableRealizationsForConst` of a constant that they unify under, where
# Lean computes its `funInfo` in the caller's state, taking names, and reused after it, where Lean
# computes it in a realization, taking none: in Lean, the search takes one name less after enabling
cat > DriftOn.lean <<'EOF'
import Lean
open Lean Meta Elab
class D (α : Type) where
def names (ty : Expr) : MetaM Nat := do
  modify ({ · with cache := {} })
  let i0 := (← getNGen).idx
  let _ ← synthInstance? ty
  return (← getNGen).idx - i0
def d (e : Expr) : Expr := mkApp (mkConst ``D) e
def t0 (e : Expr) : Expr := mkApp (mkConst `T0) e
def search : MetaM Nat :=
  withLocalDecl `i .instImplicit (.forallE `n (mkConst ``Nat) (d (t0 (.bvar 0))) .default) fun _ =>
    names (d (t0 (mkNatLit 0)))
run_meta do
  addDecl <| .axiomDecl { name := `T0, levelParams := [], isUnsafe := false
                          type := mkForall `n .default (mkConst ``Nat) (mkSort 1) }
  let a ← search
  let b ← search
  enableRealizationsForConst `T0
  let c ← search
  let e ← search
  logInfo m!"names of the same search: not enabled {a}, {b}; enabled {c}, {e}"
EOF
# ... and the other way round: recorded after enabling, and reused for a constant of the same name
# after the environment was restored, which is not enabled
cat > DriftBack.lean <<'EOF'
import Lean
open Lean Meta Elab
class D (α : Type) where
def names (ty : Expr) : MetaM Nat := do
  modify ({ · with cache := {} })
  let i0 := (← getNGen).idx
  let _ ← synthInstance? ty
  return (← getNGen).idx - i0
def addT : MetaM Unit :=
  addDecl <| .axiomDecl { name := `T0, levelParams := [], isUnsafe := false
                          type := mkForall `n .default (mkConst ``Nat) (mkSort 1) }
def d (e : Expr) : Expr := mkApp (mkConst ``D) e
def t0 (e : Expr) : Expr := mkApp (mkConst `T0) e
def search : MetaM Nat :=
  withLocalDecl `i .instImplicit (.forallE `n (mkConst ``Nat) (d (t0 (.bvar 0))) .default) fun _ =>
    names (d (t0 (mkNatLit 0)))
run_meta do
  let env ← getEnv
  addT
  enableRealizationsForConst `T0
  let a ← search
  let b ← search
  setEnv env
  addT
  let c ← search
  logInfo m!"names of the same search: enabled {a}, {b}; not enabled {c}"
EOF

for f in NsMacro NsElab NsDoElem ByElab NsDeclName QuotCtx NgenAfter TcNgen TcPure Transparent CrossNs HygNames \
    RestoredMacro RestoredHelper CacheProbe CrossNsMacro TcInDefEq TcEmptied TcLeft TcPermNames TcInGrind \
    DriftOn DriftBack; do
  set +e
  PAPERLEAN_REUSE_STATS=$f.stats lean $f.lean > $f.reuse.out 2>&1; r1=$?
  PAPERLEAN_EXACT=1 lean $f.lean > $f.exact.out 2>&1; r2=$?
  PAPERLEAN_REUSE_ORACLE=1 lean $f.lean > $f.oracle.out 2>&1
  set -e
  [ $r1 = $r2 ] && cmp -s $f.reuse.out $f.exact.out ||
    fail "$f.lean differs from a run that reuses nothing (exit $r1 vs $r2):
$(diff $f.reuse.out $f.exact.out)"
  cmp -s $f.oracle.out $f.exact.out || fail "$f.lean: the output with the oracle differs"
  # (a file whose state does not change in Lean tests nothing)
  case $f in
    NsMacro|NsElab|NsDoElem|ByElab|Restored*)
      [ "$(grep -c "Type mismatch" $f.exact.out)" = 1 ];;
    NsDeclName) [ "$(grep -c "Type mismatch" $f.exact.out)" = 1 ] &&
      grep -q "NsDeclName.lean:9:" $f.exact.out;;
    QuotCtx) [ "$(grep "^h : " $f.exact.out | sort -u | wc -l)" = 2 ];;
    NgenAfter) grep -q "294 = 290" $f.exact.out &&
      grep -q "NgenAfter.lean:7:28: error" $f.exact.out;;
    TcNgen) [ "$(grep -c "^ngen " $f.exact.out)" = 10 ] &&
      grep -q "^end ngen 2567$" $f.exact.out;;
    TcPure) grep -q "^ngen 1454, mvars 8$" $f.exact.out && grep -q "^end ngen 2078$" $f.exact.out &&
      grep -q "TcPure.lean:10:40: error: Type mismatch" $f.exact.out;;
    Transparent) grep -q "@t2 : ∀ {α : Type u_[0-9]} (a : α) (n : ℕ'), True" $f.exact.out;;
    CrossNs) grep -q "^B.C.t3 : ∀ (n : T), n = n" $f.exact.out;;
    HygNames) [ "$(grep -c "_hygCtx" $f.exact.out)" -ge 6 ];;
    CacheProbe) [ "$(grep -c "^wrong entries: 0$" $f.exact.out)" = 2 ];;
    TcPermNames) [ "$(grep -c "stale keys 0" $f.exact.out)" = 2 ];;
    DriftOn) grep -q "not enabled 4, 4; enabled 3, 3" $f.exact.out;;
    DriftBack) grep -q "enabled 3, 3; not enabled 4" $f.exact.out;;
  esac || fail "$f.lean does not test what it should: $(cat $f.exact.out)"
done
awk -F '\t' '$1 == "CrossNsMacro.lean" && $6 >= 1' CrossNsMacro.stats | grep -q . ||
  fail "variables of a macro were not reused in another namespace: $(cat CrossNsMacro.stats)"
# Lean's own elaborators, whose declarations a file that imports them has, leave the namespace alone
awk -F '\t' '$1 == "CrossNs.lean" && $6 >= 2' CrossNs.stats | grep -q . ||
  fail "variables of Lean's elaborators were not reused in other namespaces: $(cat CrossNs.stats)"
# searches reused inside an `isDefEq` (of these numbers, fewer means that they are not), and one that
# Lean's own run keeps from reuse
reused_at_least() {
  awk -F '\t' -v n=$2 '$2 >= n' $1.stats | grep -q . || fail "$1.lean reused too little: $(cat $1.stats)"
}
reused_at_least TcInDefEq 17
reused_at_least TcEmptied 31
reused_at_least TcLeft 28
grep -q "not reused: other binder names with macro scopes=[1-9]" TcPermNames.stats ||
  fail "TcPermNames.lean was not refused for its binder names: $(cat TcPermNames.stats)"
grep -q "not eligible: in .grind., under a name generator that starts again=[1-9]" TcInGrind.stats ||
  fail "TcInGrind.lean has no search under grind's name generator: $(cat TcInGrind.stats)"
# the typeclass results were reused
awk -F '\t' '$1 == "TcNgen.lean" && $2 >= 30' TcNgen.stats | grep -q . ||
  fail "TcNgen.lean reused too few typeclass results: $(cat TcNgen.stats)"
# ... also those whose lookups of pure keys find otherwise
reused_at_least TcPure 13
# a typeclass problem whose type holds the syntax of a pattern in metadata, which compares without its
# position: in Lean, each result holds the position of its own theorem, in the theorem's type
cat > PatRef.lean <<'EOF'
class Foo (α : Type) where x : Nat
instance : Foo Nat := ⟨0⟩
instance {α β : Type} [Foo α] [Foo β] : Foo (α × β) := ⟨0⟩
def useFoo {α : Type} [Foo α] (_ : α → Nat) : Prop := True
def g (a b c : Nat) : Nat := a + b + c
theorem t1 : useFoo (fun (a, b, c) ↦ g a b c) := trivial
theorem t2 : useFoo (fun (a, b, c) ↦ g a b c) := trivial
theorem t3 : useFoo (fun (a, b, c) ↦ g a b c) := trivial
EOF
lean -o pat_ref.reuse.olean PatRef.lean > pat_ref.out 2>&1 || fail "PatRef.lean: $(cat pat_ref.out)"
PAPERLEAN_EXACT=1 lean -o pat_ref.exact.olean PatRef.lean > pat_ref.out 2>&1 || fail "PatRef.lean: $(cat pat_ref.out)"
cmp -s pat_ref.reuse.olean pat_ref.exact.olean || fail "PatRef.lean: the .olean differs from a run that reuses nothing"
# Files whose output shows nothing: the `.olean`, `.ilean` and `.c` must be those of a run that reuses
# nothing. `inductive` runs `mkSizeOfInstances` before it enables the realizations of the type, so that
# its searches are recorded in that state and reused after it; every later name of the file would be
# off, which the compiler's `let` ids in `greeting._closed_1` keep.
cat > OleanDrift.lean <<'EOF'
inductive Foo (n : Nat) : Type
  | nil : Foo n
  | cons (s : Foo n) : Foo n

example (n : Nat) (a : Foo n) : sizeOf a = sizeOf a := rfl

def greeting : List String := ["hello", "world"]
EOF
# ... with no `sizeOf` in the source, through what structural recursion tries
cat > DriftRec.lean <<'EOF'
inductive Foo (n : Nat) : Type
  | nil : Foo n
  | cons (s : Foo n) : Foo n
def bar : {n : Nat} → Foo n → Foo n → Bool
  | n+1, .cons a, .cons b => bar a b
  | _, _, _ => true
def greeting : List String := ["hello", "world"]
EOF
cat > DriftMatch.lean <<'EOF'
inductive Foo (n : Nat) : Type
  | nil : Foo n
  | cons (s : Foo n) : Foo n
def bar {n : Nat} (a : Foo n) : Bool := match n, a with
  | n+1, .cons a => bar a
  | _, _ => true
def greeting : List String := ["hello", "world"]
EOF
# ... and the same searches recorded after enabling, which are reused
cat > DriftControl.lean <<'EOF'
set_option genSizeOfSpec false
inductive Foo (n : Nat) : Type
  | nil : Foo n
  | cons (s : Foo n) : Foo n
set_option genSizeOfSpec true
example (n : Nat) (a : Foo n) : sizeOf a = sizeOf a := rfl
example (n : Nat) (a : Foo n) : sizeOf a = sizeOf a := rfl
example (n : Nat) (a : Foo n) : sizeOf a = sizeOf a := rfl
def greeting : List String := ["hello", "world"]
EOF
# The numbers of the identifiers of reused section variables, which must be Lean's. A tactic that keeps
# hypotheses in a set of identifiers, in their order (`aesop`'s forward rules do, and a binder name of
# their proofs shows it): `#print` and the `.olean` hold the name that the first one gives.
cat > FVarOrder.lean <<'EOF'
import Lean
open Lean Meta Elab Tactic
elab "name_by_order" : tactic => do
  let mut s : FVarIdSet := {}
  for d in ← getLCtx do
    unless d.isImplementationDetail do s := s.insert d.fvarId
  let some id := s.toList.head? | throwError "no variables"
  let x := mkIdent ((← id.getUserName).appendAfter "_h")
  evalTactic (← `(tactic| have $x:ident : True := trivial))
variable (a b c d e f g h : Nat) (p q r s : Prop)
include a b c d e f g h p q r s
theorem t1 : True := by name_by_order; trivial
theorem t2 : True := by name_by_order; trivial
theorem t3 : True := by name_by_order; trivial
theorem t4 : True := by name_by_order; trivial
theorem t5 : True := by name_by_order; trivial
theorem t6 : True := by name_by_order; trivial
#print t1
#print t2
#print t3
#print t4
#print t5
#print t6
EOF
# ... and Verso docstrings, which store the local context and the identifier of a variable that they name
cat > VersoVar.lean <<'EOF'
set_option doc.verso true
variable (howMany : Nat)
/-- Returns how many there are (that is, {name}`howMany`). -/
def f := howMany
/-- Returns its argument (but not {name}`howMany`). -/
def g (x : Nat) := x
/-- Returns its argument (but not {name}`howMany`) again. -/
def h (x : Nat) := x
EOF
cat > VersoModuleVar.lean <<'EOF'
set_option doc.verso.module true
variable (howMany : Nat)
def f := howMany
def g (x : Nat) := x
/-! About {name}`howMany`. -/
def h (x : Nat) := x
/-! About {name}`howMany` again. -/
EOF
# Literals above 2^63, which constants added without `shareCommonPreDefs` hold: a reuse takes the
# object of an earlier command, which a bignum of its own in Lean's run is equal to.
cat > BigAxiom.lean <<'EOF'
axiom a1 : (200000000000000000000 : Nat) = 200000000000000000000
axiom a2 : (200000000000000000000 : Nat) + 1 = 200000000000000000001
axiom a3 : (200000000000000000000 : Nat) = 200000000000000000000
EOF
cat > BigInductive.lean <<'EOF'
inductive I : Nat → Type
  | mk : I 200000000000000000000
inductive J : Nat → Type
  | mk : J 200000000000000000000
structure S where
  x : Fin 200000000000000000000
structure T where
  x : Fin 200000000000000000000
EOF
cat > BigVariable.lean <<'EOF'
variable (n : Nat) (h : n = 200000000000000000000)
axiom b1 : n = 200000000000000000000
axiom b2 : n = 200000000000000000000
structure U (m : Nat) where
  x : Fin 200000000000000000000
structure V (m : Nat) where
  x : Fin 200000000000000000000
EOF
cat > BigOpaque.lean <<'EOF'
opaque o1 : Fin 200000000000000000000
opaque o2 : Fin 200000000000000000000
class K (n : Nat) where
instance : K 200000000000000000000 := ⟨⟩
instance : K 200000000000000000001 := ⟨⟩
axiom k1 : K 200000000000000000000
axiom k2 : K 200000000000000000000
EOF
# ... in all the parts of a module, which share what the compactor has seen
cat > BigModule.lean <<'EOF'
module
public axiom a1 : (200000000000000000000 : Nat) = 200000000000000000000
axiom a2 : (200000000000000000000 : Nat) = 200000000000000000000
public theorem t1 : (200000000000000000000 : Nat) = 200000000000000000000 := a2
public axiom a3 : (200000000000000000000 : Nat) = 200000000000000000000
public def big : Nat := 200000000000000000000
@[expose] public def big' : Nat := 200000000000000000001
EOF
# ... and with proofs on the elaboration thread, through the axiom of `native_decide`
cat > BigNative.lean <<'EOF'
theorem tst4 : 10000000000000000 < 200000000000000000000 := by decide
theorem tst5 : 10000000000000000 < 200000000000000000000 := by native_decide
EOF
for f in OleanDrift DriftRec DriftMatch DriftControl FVarOrder VersoVar VersoModuleVar BigAxiom BigInductive \
    BigVariable BigOpaque BigModule BigNative; do
  args=
  [ $f = BigNative ] && args=-DElab.async=false
  set +e
  PAPERLEAN_REUSE_STATS=$f.stats lean $args -o $f.reuse.olean -i $f.reuse.ilean -c $f.reuse.c $f.lean > $f.reuse.out 2>&1
  r1=$?
  PAPERLEAN_EXACT=1 lean $args -o $f.exact.olean -i $f.exact.ilean -c $f.exact.c $f.lean > $f.exact.out 2>&1
  r2=$?
  PAPERLEAN_REUSE_ORACLE=1 lean $args $f.lean > $f.oracle.out 2>&1
  r3=$?
  set -e
  [ "$r1 $r2 $r3" = "0 0 0" ] || fail "$f.lean (exit $r1, $r2, $r3): $(cat $f.reuse.out $f.exact.out $f.oracle.out)"
  cmp -s $f.reuse.out $f.exact.out || fail "$f.lean: the output differs: $(diff $f.reuse.out $f.exact.out)"
  for x in olean ilean c olean.server olean.private; do
    [ ! -e $f.exact.$x ] || cmp $f.reuse.$x $f.exact.$x ||
      fail "$f.lean: the .$x differs from a run that reuses nothing"
  done
done
grep -q "greeting___closed__1" OleanDrift.exact.c || fail "OleanDrift.lean does not test what it should"
for f in OleanDrift DriftRec DriftMatch DriftControl FVarOrder VersoVar BigAxiom BigInductive BigVariable BigOpaque \
    BigModule; do
  awk -F '\t' '$2 >= 1 || $6 >= 1' $f.stats | grep -q . || fail "$f.lean reused nothing: $(cat $f.stats)"
done
[ -e BigModule.exact.olean.private ] || fail "BigModule.lean does not test what it should"
# the literals of a module are read back, also where a part points into another
cat > UseBig.lean <<'EOF'
module
import all BigModule
#print a1
#print a2
#print t1
#eval big + 1
#eval big'
example : (200000000000000000000 : Nat) = 200000000000000000000 := a2
EOF
for x in olean olean.server olean.private; do cp BigModule.reuse.$x BigModule.$x; done
LEAN_PATH=.:${LEAN_PATH:-} lean UseBig.lean > use_big.out 2>&1 || fail "UseBig.lean: $(cat use_big.out)"
[ "$(grep -c "200000000000000000000 = 200000000000000000000" use_big.out)" = 3 ] &&
  grep -q "^200000000000000000001$" use_big.out || fail "UseBig.lean: $(cat use_big.out)"
# what is compacted is the same value, and the sign of a bignum is part of it
cat > BigSigned.lean <<'EOF'
import Lean
open Lean
unsafe def main : IO Unit := do
  let n ← IO.mkRef (70 : Nat)
  let e ← n.get
  -- (two ways, of which the compiler keeps two objects)
  let big (d : Int) : Int := 2 ^ e + d
  let big' (d : Int) : Int := 2 ^ (e - 1) * 2 + d
  let xs : Array Int := #[big 0, -big 0, big 1, big' 0, -big' 0, big' 1]
  let data : ModuleData := { imports := #[], constNames := #[], constants := #[], extraConstNames := #[]
                             entries := #[(`x, unsafeCast xs)], isModule := false }
  saveModuleData "BigSigned.olean" `BigSigned data
  let (r, _) ← readModuleData "BigSigned.olean"
  let ys : Array Int := unsafeCast r.entries[0]!.2
  IO.println (ys == xs)
  let same (i j : Nat) := ptrAddrUnsafe ys[i]! == ptrAddrUnsafe ys[j]!
  IO.println s!"{same 0 3} {same 1 4} {same 2 5} {same 0 1} {same 0 2}"
#eval main
EOF
lean BigSigned.lean > big_signed.out 2>&1 || fail "BigSigned.lean: $(cat big_signed.out)"
[ "$(cat big_signed.out)" = "true
true true true false false" ] || fail "BigSigned.lean: $(cat big_signed.out)"
# what PaperLean does not support stops with an error that names it: a builtin registered at run
# time. With nothing reused, it is Lean's.
cat > AddBuiltin.lean <<'EOF'
import Lean
open Lean Elab Command
syntax (name := curNs) "curNs%" : term
@[macro curNs] def nsMacro : Macro := fun _ => do
  return (quote (← Macro.getCurrNamespace) : TSyntax `term).raw
run_cmd liftIO <| macroAttribute.addBuiltin ``curNs ``nsMacro nsMacro
EOF
PAPERLEAN_EXACT=1 lean AddBuiltin.lean > add_builtin_exact.out 2>&1 ||
  fail "AddBuiltin.lean does not test what it should: $(cat add_builtin_exact.out)"
lean AddBuiltin.lean > add_builtin.out 2>&1 && fail "a builtin was registered at run time"
grep -q "PaperLean does not support registering a builtin at run time (nsMacro); build this file with .lake build." \
  add_builtin.out || fail "AddBuiltin.lean did not say what is not supported: $(cat add_builtin.out)"
# an elaborator that changes the heartbeat counter is one that is not on the whitelist
cat > SetHeartbeats.lean <<'EOF'
import Lean.Elab.ElabRules
open Lean Elab Term
elab "resetHeartbeats%" : term => do
  IO.setNumHeartbeats 0
  return mkConst ``Nat
variable (n : resetHeartbeats%)
theorem t1 : n = n := rfl
theorem t2 : n = n := rfl
EOF
PAPERLEAN_REUSE_STATS=set_heartbeats.stats lean SetHeartbeats.lean > set_heartbeats.out 2>&1 ||
  fail "SetHeartbeats.lean: $(cat set_heartbeats.out)"
grep -q "ResetHeartbeats.*not on the whitelist" set_heartbeats.stats ||
  fail "SetHeartbeats.lean does not say why: $(cat set_heartbeats.stats)"
