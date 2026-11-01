# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests the reuse of typeclass results across commands (`Lean.PaperLean.TCCache`): the output is Lean
# 4.35.0-rc3's (the expected output below is official Lean's) for theorems of a section that solve
# the same problems, a theorem with another local instance of the class (another problem, whose
# result is another instance), and problems whose result an instance added later changes (with a
# lower priority, which does not change the result, and a higher one, which does); results are
# reused; and every reuse agrees with Lean's search (`PAPERLEAN_REUSE_ORACLE`), which the oracle
# repeats for it, comparing also the names it takes and its entries in Lean's caches. Also that the
# problem's visibility, binder annotations, kinds of local declarations and let-variables to unfold
# (`zetaDeltaSet`) are part of it, and the macro scopes of binder names where the search put them
# into the keys or values of Lean's caches. And that results stay reusable after instances of other
# classes, and not after an instance of the class or an erased one; and that problems whose context
# has assigned metavariables, or with metavariables only in output parameters, are reused; and that
# a search's lookups in Lean's caches whose value is a function of the key need not find what they
# found. And that linters, which run in tasks with the command's environment, neither use nor fill
# the caches of typeclass results and section variables.

export PAPERLEAN_REUSE=1

cat > "$TMP_DIR/TCCache.lean" <<'EOF'
class Foo (α : Type) where
  foo : α
class Bar (α : Type) extends Foo α where
  bar : α
instance : Foo Nat := ⟨0⟩

section
variable {α : Type} [Bar α] [Add α]
theorem t1 (x : α) : x + Foo.foo = x + Foo.foo := rfl
theorem t2 (y : α) : y + Foo.foo = y + Foo.foo := rfl
theorem t3 (z : α) : Foo.foo + z = Foo.foo + z := rfl
-- another local instance of the class: another problem
theorem t4 [inst : Foo α] : (Foo.foo : α) = @Foo.foo α inst := rfl
theorem t5 : (Foo.foo : α) = @Foo.foo α Bar.toFoo := rfl
#check @t3
#check @t4
end

example : (Foo.foo : Nat) = 0 := rfl
example : (Foo.foo : Nat) = 0 := rfl
instance (priority := low) fooNat1 : Foo Nat := ⟨1⟩
example : (Foo.foo : Nat) = 0 := rfl
-- an instance that Lean prefers: the earlier result no longer holds
instance (priority := high) fooNat2 : Foo Nat := ⟨2⟩
example : (Foo.foo : Nat) = 2 := rfl
example : (Foo.foo : Nat) = 2 := rfl
#check (Foo.foo : Nat)
EOF
cat > "$TMP_DIR/expected.out" <<'EOF'
TCCache.lean:13:0: warning: automatically included section variable(s) unused in theorem `t4`:
  [Bar α]
  [Add α]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [Bar α] [Add α] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
TCCache.lean:14:0: warning: automatically included section variable(s) unused in theorem `t5`:
  [Add α]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [Add α] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
@t3 : ∀ {α : Type} [inst : Bar α] [inst_1 : Add α] (z : α), Foo.foo + z = Foo.foo + z
@t4 : ∀ {α : Type} [Bar α] [Add α] [inst : Foo α], Foo.foo = Foo.foo
Foo.foo : Nat
EOF
cd "$TMP_DIR"
capture_exit 0 lean TCCache.lean
$DIFF -- expected.out "$CAPTURED.out.produced" || fail "the output differs from Lean's"
# every reuse agrees with Lean's search
PAPERLEAN_REUSE_ORACLE=1 lean TCCache.lean > oracle.out 2>&1 || fail "lean failed: $(cat oracle.out)"
$DIFF -- expected.out oracle.out || fail "the output with the oracle differs from Lean's"
# a reused search of 30 steps costs few heartbeats, and the oracle compares the reuse with Lean's
# search: with a fault put in on purpose, it finds a difference and `lean` fails
{
  echo "import Lean"; echo "open Lean Meta"
  for i in $(seq 0 30); do echo "class C$i (α : Type) : Prop where"; done
  echo "instance : C0 Nat := ⟨⟩"
  for i in $(seq 1 30); do echo "instance [C$((i - 1)) α] : C$i α := ⟨⟩"; done
  echo 'run_meta discard <| synthInstance (.app (.const ``C30 []) (.const ``Nat []))'
  echo 'run_meta do'
  echo '  let (r, _, _) ← PaperLean.TCCache.stats'
  echo '  let h ← IO.getNumHeartbeats'
  echo '  discard <| synthInstance (.app (.const ``C30 []) (.const ``Nat []))'
  echo '  let h'"'"' ← IO.getNumHeartbeats'
  echo '  let (r'"'"', _, _) ← PaperLean.TCCache.stats'
  echo '  logInfo m!"reused {r'"'"' - r}, heartbeats {h'"'"' - h}"'
} > Repeat.lean
heartbeats() { sed -n "s/.*reused $1, heartbeats \([0-9]*\).*/\1/p" "$2"; }
lean Repeat.lean > repeat.out 2>&1 || fail "Repeat.lean failed: $(cat repeat.out)"
PAPERLEAN_REUSE_ORACLE=1 lean Repeat.lean > repeat_oracle.out 2>&1 || fail "Repeat.lean failed: $(cat repeat_oracle.out)"
PAPERLEAN_EXACT=1 lean Repeat.lean > repeat_exact.out 2>&1 || fail "Repeat.lean failed: $(cat repeat_exact.out)"
REUSE=$(heartbeats 1 repeat.out); SEARCH=$(heartbeats 0 repeat_exact.out)
[ -n "$REUSE" ] && [ -n "$SEARCH" ] || fail "no reuse to compare: $(cat repeat.out repeat_exact.out)"
[ $REUSE -lt $((SEARCH / 2)) ] || fail "the reuse cost $REUSE heartbeats, the search $SEARCH"
grep -q "reused 1," repeat_oracle.out || fail "nothing was reused with the oracle: $(cat repeat_oracle.out)"
PAPERLEAN_REUSE_FAULT=tc-names PAPERLEAN_REUSE_ORACLE=1 lean Repeat.lean > fault.out 2>&1 &&
  fail "the oracle did not compare the reuse: $(cat fault.out)"
grep -q "the reuse oracle found a difference: typeclass cache: Lean's search takes [0-9]* names" fault.out ||
  fail "the oracle did not say what differs: $(cat fault.out)"
PAPERLEAN_REUSE_FAULT=tc-names lean Repeat.lean > fault.out 2>&1 || fail "a fault was put in without the oracle: $(cat fault.out)"
# results were reused
{ echo "import Lean"; cat TCCache.lean; echo 'run_cmd do let (r, n, f) ← Lean.PaperLean.TCCache.stats; Lean.logInfo m!"reused {r}, searched {n}, of them after a change {f}"'; } > Stats.lean
lean Stats.lean > stats.out 2>&1
R=$(sed -n 's/.*reused \([0-9]*\), searched \([0-9]*\), of them after a change \([0-9]*\).*/\1 \3/p' stats.out)
set -- $R
[ -n "${1:-}" ] && [ "$1" -ge 3 ] || fail "too few reuses: $(tail -2 stats.out)"
[ "${2:-0}" -ge 1 ] || fail "the change of instances was not noticed: $(tail -2 stats.out)"
# the run after a failed check reuses nothing
PAPERLEAN_EXACT=1 lean Stats.lean > exact.out 2>&1
grep -q "reused 0," exact.out || fail "the exact run reused: $(tail -2 exact.out)"
# a reuse keeps the caches of the command (`modifyEnv` of `MetaM` clears them)
cat > KeepCache.lean <<'EOF2'
import Lean
open Lean Meta
class Baz (α : Type) where
  baz : α
instance : Baz Nat := ⟨0⟩
instance : Baz Int := ⟨0⟩
run_meta discard <| synthInstance (.app (.const ``Baz []) (.const ``Nat []))
run_meta do
  discard <| synthInstance (.app (.const ``Baz []) (.const ``Int []))
  let (r, n, _) ← PaperLean.TCCache.stats
  discard <| synthInstance (.app (.const ``Baz []) (.const ``Nat []))
  let (r', n', _) ← PaperLean.TCCache.stats
  -- found in the cache of the command, which the reuse kept
  discard <| synthInstance (.app (.const ``Baz []) (.const ``Int []))
  let (r'', n'', _) ← PaperLean.TCCache.stats
  logInfo m!"reused {r' - r}, searched {n' - n}, then {r'' - r' + (n'' - n')}"
EOF2
lean KeepCache.lean > keep.out 2>&1
grep -q 'reused 1, searched 0, then 0$' keep.out || fail "a reuse lost the caches of the command: $(cat keep.out)"
# the visibility is part of the problem: a private instance is a candidate only where private
# constants are visible, so a result of a public theorem's signature is not reused in a private one
cat > VisA.lean <<'EOF2'
module
public class Foo (α : Type) : Type where
  val : Nat
public instance (priority := low) instFooPub : Foo Nat := ⟨2⟩
private instance instFooPriv : Foo Nat := ⟨1⟩
EOF2
for v in 1 2; do
  cat > VisB$v.lean <<EOF2
module
public import VisA
import all VisA
public theorem pub : Foo.val Nat = Foo.val Nat := rfl
private theorem priv : Foo.val Nat = $v := rfl
EOF2
done
lean --root=. -o VisA.olean VisA.lean || fail "VisA.lean failed"
LEAN_PATH="$TMP_DIR" lean --root=. VisB1.lean > vis1.out 2>&1 ||
  fail "the private theorem did not see the private instance: $(cat vis1.out)"
LEAN_PATH="$TMP_DIR" lean --root=. VisB2.lean > vis2.out 2>&1 &&
  fail "the private theorem took the public instance, which Lean does not"
grep -q "Not a definitional equality" vis2.out || fail "VisB2.lean failed otherwise than in Lean: $(cat vis2.out)"
# binder annotations are part of the problem: the subgoals of a local instance come from its
# instance-implicit binders, so `[_h : Foo n]` and `(_h : Foo n)` give different results, in both
# orders
cat > Binders1.lean <<'EOF2'
class Foo (n : Nat) : Prop where
class Bar (n : Nat) : Prop where
instance : Foo 0 := ⟨⟩
example (inst : ∀ {n : Nat} [_h : Foo n], Bar n) : Bar 0 := inferInstance
example (inst : ∀ {n : Nat} (_h : Foo n), Bar n) : Bar 0 := inferInstance
EOF2
lean Binders1.lean > binders1.out 2>&1 && fail "a result for an instance-implicit binder was reused for an explicit one"
grep -q "failed to synthesize" binders1.out || fail "Binders1.lean failed otherwise than in Lean: $(cat binders1.out)"
cat > Binders2.lean <<'EOF2'
class Foo (n : Nat) : Prop where
class Bar (n : Nat) : Prop where
instance : Foo 0 := ⟨⟩
example (inst : ∀ {n : Nat} (_h : Foo n), Bar n) : Bar 0 := by first | exact inferInstance | exact inst ⟨⟩
example (inst : ∀ {n : Nat} [_h : Foo n], Bar n) : Bar 0 := inferInstance
EOF2
lean Binders2.lean > binders2.out 2>&1 || fail "a failure for an explicit binder was reused for an instance-implicit one: $(cat binders2.out)"
# binder names are part of the problem only up to macro scopes, which differ from command to command
# (e.g. of `(· < 3)`), while binder infos are part of it; a result whose search put the binder name
# into an entry of Lean's caches (here the type of the function) is reused only for the same names
cat > Hygiene.lean <<'EOF2'
import Lean
open Lean Meta
class Foo (p : Nat → Prop) : Prop where
instance : Foo (fun x => x = x) := ⟨⟩
/-- `Foo (fun x => x = x)` with a binder name with macro scope `s` and binder info `bi`. -/
def prob (s : Nat) (bi : BinderInfo) : Expr :=
  .app (.const ``Foo []) (.lam (Lean.addMacroScope `M `x s) (.const ``Nat [])
    (mkApp3 (.const ``Eq [1]) (.const ``Nat []) (.bvar 0) (.bvar 0)) bi)
/-- Solves `prob s bi` and reports whether the result was reused. -/
def solve (s : Nat) (bi : BinderInfo) : MetaM Unit := do
  let (r, n, _) ← PaperLean.TCCache.stats
  discard <| synthInstance (prob s bi)
  let (r', n', _) ← PaperLean.TCCache.stats
  logInfo m!"reused {r' - r}, searched {n' - n}"
run_meta solve 1 .default
run_meta solve 1 .default
run_meta solve 2 .default
run_meta solve 3 .implicit
EOF2
lean Hygiene.lean > hygiene.out 2>&1 || fail "Hygiene.lean failed: $(cat hygiene.out)"
printf 'reused 0, searched 1\nreused 1, searched 0\nreused 0, searched 1\nreused 0, searched 1\n' |
  $DIFF -- - hygiene.out ||
  fail "a problem was reused with other binder names in its cache entries, or across binder infos"
# also where the binder name is only in the keys of the search's operations on Lean's caches (here
# `inferType ((let x := 0; (0, 0)).1) ↦ Nat`): the caches of `inferType` and `whnf` compare keys
# with their binder names, so a reuse for other names would look up and insert other keys than
# Lean's search (the oracle sees that: it compares the keys that a reuse inserts with Lean's)
cat > KeyNames.lean <<'EOF2'
import Lean
open Lean Meta
class Foo8 (α : Type) (n : Nat) : Prop where
instance (α : Type) : Foo8 α 0 := ⟨⟩
/-- `(let x := 0; (0, 0)).1` with a binder name with macro scope `s`. -/
def arg (s : Nat) : Expr :=
  .proj ``Prod 0 (.letE (Lean.addMacroScope `M `x s) (.const ``Nat []) (mkNatLit 0)
    (mkApp4 (.const ``Prod.mk [0, 0]) (.const ``Nat []) (.const ``Nat []) (mkNatLit 0) (mkNatLit 0))
    false)
/-- Solves `Foo8 α (arg s)` and reports whether the result was reused. -/
def solve (s : Nat) : MetaM Unit :=
  withLocalDeclD `α (.sort 1) fun α => do
    let (r, n, _) ← PaperLean.TCCache.stats
    discard <| synthInstance (mkApp2 (.const ``Foo8 []) α (arg s))
    let (r', n', _) ← PaperLean.TCCache.stats
    logInfo m!"reused {r' - r}, searched {n' - n}"
run_meta solve 1
run_meta solve 1
run_meta solve 2
run_meta solve 2
EOF2
printf 'reused 0, searched 1\nreused 1, searched 0\nreused 0, searched 1\nreused 1, searched 0\n' \
  > key_names.expected
lean KeyNames.lean > key_names.out 2>&1 || fail "KeyNames.lean failed: $(cat key_names.out)"
$DIFF -- key_names.expected key_names.out ||
  fail "a problem was reused with other binder names in the keys of its cache entries"
PAPERLEAN_REUSE_ORACLE=1 lean KeyNames.lean \
  > key_names_oracle.out 2>&1 || fail "KeyNames.lean failed with the oracle: $(cat key_names_oracle.out)"
$DIFF -- key_names.expected key_names_oracle.out || fail "KeyNames.lean: the output with the oracle differs"
# whether `inferType` uses Lean's cache (`Meta.Context.cacheInferType`) is part of the problem: a
# search with it off makes no operations on that cache, and one with it on does; in either order,
# and the oracle finds no difference
printf 'reused 0, searched 1\nreused 0, searched 1\nreused 1, searched 0\nreused 1, searched 0\n' \
  > cache_flag.expected
for order in "true false" "false true"; do
  set -- $order
  sed -e '/^run_meta solve/d' \
    -e 's/^def solve (s : Nat) : MetaM Unit :=/def solve (s : Nat) (cacheIt : Bool) : MetaM Unit :=\
  withReader (fun ctx => { ctx with cacheInferType := cacheIt }) <|/' KeyNames.lean > CacheFlag.lean
  printf 'run_meta solve 1 %s\n' $1 $2 $1 $2 >> CacheFlag.lean
  grep -q "cacheInferType := cacheIt" CacheFlag.lean || fail "CacheFlag.lean was not made"
  lean CacheFlag.lean > cache_flag.out 2>&1 ||
    fail "CacheFlag.lean ($order) failed: $(cat cache_flag.out)"
  $DIFF -- cache_flag.expected cache_flag.out ||
    fail "a result was reused with another \`cacheInferType\` ($order)"
  PAPERLEAN_REUSE_ORACLE=1 lean CacheFlag.lean > cache_flag_oracle.out 2>&1 ||
    fail "CacheFlag.lean ($order) failed with the oracle: $(cat cache_flag_oracle.out)"
  $DIFF -- cache_flag.expected cache_flag_oracle.out ||
    fail "CacheFlag.lean ($order): the output with the oracle differs"
done
# the kinds of the local declarations are part of the problem (an implementation detail is no local
# instance)
cat > Kinds.lean <<'EOF2'
import Lean
open Lean Meta
class Baz : Prop where
/-- Solves `Baz` with a local instance of kind `kind` and reports whether the result was reused. -/
def solveIn (kind : LocalDeclKind) : MetaM Unit :=
  withLocalDecl `inst .instImplicit (mkConst ``Baz) (kind := kind) fun _ => do
    let (r, n, _) ← PaperLean.TCCache.stats
    discard <| synthInstance (mkConst ``Baz)
    let (r', n', _) ← PaperLean.TCCache.stats
    logInfo m!"reused {r' - r}, searched {n' - n}"
run_meta solveIn .default
run_meta solveIn .default
run_meta solveIn .implDetail
EOF2
lean Kinds.lean > kinds.out 2>&1 && fail "a result was reused for a local declaration of another kind"
printf 'reused 0, searched 1\nreused 1, searched 0\n' | $DIFF -- - <(head -2 kinds.out) ||
  fail "Kinds.lean: unexpected reuses: $(cat kinds.out)"
grep -q "failed to synthesize" kinds.out || fail "Kinds.lean failed otherwise than in Lean: $(cat kinds.out)"
# let-variables to unfold (`zetaDeltaSet`, here with `zetaDelta := false`) decide results: the expected
# output is official Lean's
cat > ZetaDelta.lean <<'EOF2'
import Lean
open Lean Meta

class Bar (α : Type) : Prop where
class Foo (α : Type) : Prop where

/-- In a context `x : Type := List Nat`, `[Bar (List Nat)]`, `[[Bar x] → Foo Nat]`, with
`zetaDelta := false`, synthesizes `Foo Nat`, with `x` to unfold (`zetaDeltaSet`) if `useSet`. -/
def runIt (useSet : Bool) : MetaM Bool := do
  let listNat ← mkAppM ``List #[mkConst ``Nat]
  withLetDecl `x (mkSort Level.one) listNat fun x => do
  withLocalDecl `li2 .instImplicit (mkApp (mkConst ``Bar) listNat) fun _ => do
  let liTy ← withLocalDecl `h .instImplicit (mkApp (mkConst ``Bar) x) fun h =>
    mkForallFVars #[h] (mkApp (mkConst ``Foo) (mkConst ``Nat))
  withLocalDecl `li .instImplicit liTy fun _ => do
  withConfig (fun c => { c with zetaDelta := false }) do
  let go : MetaM Bool := do return (← synthInstance? (mkApp (mkConst ``Foo) (mkConst ``Nat))).isSome
  if useSet then withZetaDeltaSet ((({} : FVarIdSet).insert x.fvarId!)) go else go

run_meta do logInfo m!"without x: {← runIt false}"
run_meta do logInfo m!"with x: {← runIt true}"
run_meta do logInfo m!"without x: {← runIt false}"
run_meta do logInfo m!"with x: {← runIt true}"
EOF2
lean ZetaDelta.lean > zeta_delta.out 2>&1 || fail "ZetaDelta.lean failed: $(cat zeta_delta.out)"
printf 'without x: false\nwith x: true\nwithout x: false\nwith x: true\n' | $DIFF -- - zeta_delta.out ||
  fail "a result was reused across let-variables to unfold"
# a search depends on the instances of the classes of its goals only; problems whose context has
# assigned metavariables (theorem-level instance binders) and problems with metavariables only in
# output parameters are reused; the output is Lean's (the expected output is official Lean's)
cat > Deps.lean <<'EOF2'
class Base (α : Type) where
  b : α
class Dep (α : Type) [Base α] where
  d : α
class Res (α : Type) where
  r : α
instance {α} [Base α] [Dep α] : Res α := ⟨Dep.d⟩
class Conv (α : Type) (β : outParam Type) where
  conv : α → β
instance : Conv Nat Int := ⟨Int.ofNat⟩
def useConv {α β} [Conv α β] (a : α) : β := Conv.conv a
-- theorem-level instance binders (the type of `[Dep α]` has a metavariable assigned `Base α`)
theorem b1 {α : Type} [Base α] [Dep α] : (Res.r : α) = Res.r := rfl
-- an instance of another class
instance : Inhabited (Fin 3 → Nat) := ⟨fun _ => 0⟩
theorem b2 {α : Type} [Base α] [Dep α] : (Res.r : α) = Res.r := rfl
-- a metavariable only in an output parameter
theorem c1 (n : Nat) : useConv n = useConv n := rfl
theorem c2 (n : Nat) : useConv n = useConv n := rfl
example : useConv (3 : Nat) = (3 : Int) := rfl
-- an instance of the class, which changes the result
instance (priority := high) : Conv Nat Nat := ⟨id⟩
example : useConv (3 : Nat) = (3 : Nat) := rfl
#check useConv (3 : Nat)
class Baz (n : Nat) where
  val : Nat
instance bazA : Baz 0 := ⟨1⟩
example : Baz.val 0 = 1 := rfl
-- an erased instance
attribute [-instance] bazA
example : Baz.val 0 = 1 := rfl
EOF2
cat > deps.expected <<'EOF2'
useConv 3 : Nat
Deps.lean:31:10: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Baz 0

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
EOF2
lean Deps.lean > deps.out 2>&1 && fail "Deps.lean did not fail as in Lean"
$DIFF -- deps.expected deps.out || fail "Deps.lean: the output differs from Lean's"
PAPERLEAN_REUSE_ORACLE=1 lean Deps.lean > deps_oracle.out 2>&1 &&
  fail "Deps.lean did not fail with the oracle"
$DIFF -- deps.expected deps_oracle.out || fail "Deps.lean: the output with the oracle differs from Lean's"
{ echo "import Lean"; cat Deps.lean; echo 'run_cmd do let (r, n, f) ← Lean.PaperLean.TCCache.stats; Lean.logInfo m!"reused {r}, searched {n}, of them after a change {f}"'; } > DepsStats.lean
lean DepsStats.lean > deps_stats.out 2>&1 || true
R=$(sed -n 's/.*reused \([0-9]*\), searched \([0-9]*\), of them after a change \([0-9]*\).*/\1 \3/p' deps_stats.out)
set -- $R
# (12: without the reuses of `b2` 10, without those of `c2` 11)
[ -n "${1:-}" ] && [ "$1" -ge 12 ] || fail "too few reuses: $(tail -2 deps_stats.out)"
[ "${2:-0}" -ge 2 ] || fail "the changes of instances were not noticed: $(tail -2 deps_stats.out)"
# erased instances are compared by their members: an instance added after many were erased copies
# the erased set, which keeps the earlier results of other classes reusable
{
  echo "import Lean"; echo "open Lean Meta"
  for i in $(seq 0 39); do echo "class E$i (α : Type) where"; echo "instance e$i : E$i Nat := ⟨⟩"; done
  for i in $(seq 0 39); do echo "attribute [-instance] e$i"; done
  echo "class Q (n : Nat) : Prop where"
  echo "instance : Q 0 := ⟨⟩"
  echo 'def solve : MetaM Unit := do'
  echo '  let (r, n, _) ← PaperLean.TCCache.stats'
  echo '  discard <| synthInstance (mkApp (mkConst ``Q) (mkNatLit 0))'
  echo '  let (r'"'"', n'"'"', _) ← PaperLean.TCCache.stats'
  echo '  logInfo m!"reused {r'"'"' - r}, searched {n'"'"' - n}"'
  echo "run_meta solve"
  echo "instance : Inhabited (Fin 3 → Nat) := ⟨fun _ => 0⟩"
  echo "run_meta solve"
} > Erased.lean
lean Erased.lean > erased.out 2>&1 || fail "Erased.lean failed: $(cat erased.out)"
printf 'reused 0, searched 1\nreused 1, searched 0\n' | $DIFF -- - erased.out ||
  fail "a result was not reused after an instance was added with erased instances"
# a lookup in Lean's caches whose value is a function of its key (here `funInfo` of imported
# constants, which Lean computes once per module with `realizeValue`) need not find what it found:
# `Nat` is reused although the `funInfo` entries that its search found (inserted by the search for
# `Int` before it) are missing, and the second `Bool` although they are there where its search
# inserted them; the oracle finds no difference
cat > Pure.lean <<'EOF2'
import Lean
open Lean Meta
/-- Solves `Inhabited (List α)` and reports whether the result was reused. -/
def solve (α : Name) : MetaM Unit := do
  let (r, n, _) ← PaperLean.TCCache.stats
  let type := mkApp (.const ``Inhabited [1]) (mkApp (.const ``List [0]) (.const α []))
  discard <| synthInstance type
  let (r', n', _) ← PaperLean.TCCache.stats
  logInfo m!"{α}: reused {r' - r}, searched {n' - n}"
run_meta do solve ``Int; solve ``Nat
run_meta solve ``Nat
run_meta solve ``Bool
run_meta do solve ``Int; solve ``Bool
EOF2
printf '%s\n' "Int: reused 0, searched 1" "Nat: reused 0, searched 1" "Nat: reused 1, searched 0" \
  "Bool: reused 0, searched 1" "Int: reused 1, searched 0" "Bool: reused 1, searched 0" \
  > pure.expected
lean Pure.lean 2>&1 | sed 's/^.*info: //' > pure.out || fail "Pure.lean failed: $(cat pure.out)"
$DIFF -- pure.expected pure.out ||
  fail "a problem was not reused for other entries of pure keys in Lean's caches"
PAPERLEAN_REUSE_ORACLE=1 lean Pure.lean 2>&1 |
  sed 's/^.*info: //' > pure_oracle.out || fail "Pure.lean failed with the oracle"
$DIFF -- pure.expected pure_oracle.out || fail "Pure.lean: the output with the oracle differs"
# a linter's search is not kept: the same search of a later command is not reused
cat > Linter.lean <<'EOF2'
import Lean
open Lean Elab Command Meta
def problem : Expr :=
  mkApp (.const ``Inhabited [1]) (mkApp (.const ``Array [0]) (mkApp (.const ``Array [0]) (.const ``Nat [])))
run_cmd liftIO <| addLinter { name := `tcProbe, run := fun _ => do
  discard <| liftTermElabM <| synthInstance? problem
  IO.FS.writeFile "linted" "" }
theorem a : True := trivial
run_cmd do
  while !(← System.FilePath.pathExists "linted") do IO.sleep 10
  let (r, _, _) ← PaperLean.TCCache.stats
  discard <| liftTermElabM <| synthInstance? problem
  let (r', _, _) ← PaperLean.TCCache.stats
  logInfo m!"reused {r' - r}"
EOF2
lean Linter.lean > linter.out 2>&1 || fail "Linter.lean failed: $(cat linter.out)"
grep -q "reused 0" linter.out || fail "a linter's search was kept: $(cat linter.out)"
# nor do the section variables of a linter count: those of the commands are as without it
{ cat <<'EOF2'
import Lean
open Lean Elab Command Meta
EOF2
  echo '--LINTER'
  cat <<'EOF2'
variable (n : Nat) (h : n = n)
theorem a : n = n := rfl
theorem b : n = n := rfl
theorem c : n = n := rfl
EOF2
} > NoLinter.lean
sed 's/^--LINTER$/run_cmd liftIO <| addLinter { name := `svProbe, run := fun _ => runTermElabM fun _ => pure () }/' \
  NoLinter.lean > SvLinter.lean
PAPERLEAN_REUSE_STATS=sv_linter.stats lean SvLinter.lean > sv_linter.out 2>&1 ||
  fail "SvLinter.lean failed: $(cat sv_linter.out)"
PAPERLEAN_REUSE_STATS=no_linter.stats lean NoLinter.lean > no_linter.out 2>&1 ||
  fail "NoLinter.lean failed: $(cat no_linter.out)"
[ "$(cut -f6-8 sv_linter.stats)" = "$(cut -f6-8 no_linter.stats)" ] ||
  fail "a linter used the section variables' entries: $(cat sv_linter.stats no_linter.stats)"
