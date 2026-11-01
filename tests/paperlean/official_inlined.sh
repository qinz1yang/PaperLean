# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that an imported elaborator that is not on the whitelist (`Lean.PaperLean.Whitelist`) gives official
# Lean's result, whatever it reads and however it reads it: a recording that runs it is not used. Official
# Lean compiled these elaborators with Lean's functions that read the environment inlined
# (`compiler.small`), which then read its fields themselves, where no hook of a recording sees them:
# constants, extensions, classes and reducibility, namespaces, the constant map, in an elaborator, in a
# helper of another module, in a closure of a reference or of an extension, in polymorphic code, called
# by an elaborator of the file, in a `module`, whose code is in `.olean.private`, in code that Lean's own
# functions run from their tables (simprocs and what an `initialize` registers), and in what a tactic
# reaches. For each, a file that official Lean rejects after a change of the environment (exit code and
# output as official Lean's, also in `PAPERLEAN_EXACT=1`, and rejected with reuse), and one that it accepts
# (the same, and the `.olean` of a run that reuses nothing). Each says why in the statistics, and
# `paperlean build` says it in its summary. It needs official Lean, at `$OFFICIAL_LEAN_TOOLCHAIN` or
# elan's, and fails without it.

OFFICIAL=${OFFICIAL_LEAN_TOOLCHAIN:-$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3}
[ -x "$OFFICIAL/bin/lean" ] ||
  fail "official Lean 4.35.0-rc3 is not at $OFFICIAL (set OFFICIAL_LEAN_TOOLCHAIN to where it is)"
export XDG_CACHE_HOME="$(cd "$TMP_DIR" && pwd -P)/cache"
cd "$TMP_DIR"
official() { "$OFFICIAL/bin/lean" "$@"; }
export LEAN_PATH=$PWD/lib
mkdir -p lib

# An elaborator of a proposition, `False` when `$1` holds of `env`, compiled by official Lean with
# `compiler.small` `$2` into the module `$3`; `$4`: other declarations before it.
elaborator() {
  cat > "$3.lean" <<EOF
import Lean
open Lean Meta Elab Term
set_option compiler.small $2
set_option maxHeartbeats 0
$4
elab "chooseProp%" : term => do
  let env ← getEnv
  return mkConst (if $1 then \`\`False else \`\`True)
EOF
  official -o "lib/$3.olean" "$3.lean" > build.out 2>&1 ||
    fail "$3.lean failed under official Lean: $(cat build.out)"
}

# <file> <module> <the change of the environment> <what a reuse says>: the file with and without the
# change, under official Lean, exact and reuse
check() {
  local f=$1 m=$2 change=$3 why=$4 v r1 r2 r3
  for v in Rejected Accepted; do
    {
      echo "import $m"
      echo "variable (h : chooseProp%)"
      echo "include h"
      echo "theorem t1 : True := h"
      echo "theorem t2 : True := h"
      if [ $v = Rejected ]; then echo "$change"; fi
      echo "theorem t3 : True := h"
      echo "#check @t2"
    } > $f$v.lean
    set +e
    official -DmaxHeartbeats=0 -DmaxRecDepth=0 $f$v.lean > $f.official.out 2>&1; r1=$?
    PAPERLEAN_EXACT=1 lean -DmaxHeartbeats=0 -DmaxRecDepth=0 -o $f.exact.olean $f$v.lean \
      > $f.exact.out 2>&1; r2=$?
    PAPERLEAN_REUSE=1 PAPERLEAN_REUSE_STATS=$f$v.stats lean -DmaxHeartbeats=0 -DmaxRecDepth=0 \
      -o $f.reuse.olean $f$v.lean > $f.reuse.out 2>&1; r3=$?
    set -e
    if [ $v = Rejected ]; then
      [ $r1 = 1 ] || fail "$f: official Lean does not reject the file: $(cat $f.official.out)"
      [ $r2 = 1 ] && [ $r3 = 1 ] || fail "$f: a file that official Lean rejects, exact $r2, reuse $r3: $(cat $f.reuse.out)"
    else
      [ $r1 = 0 ] && [ $r2 = 0 ] && [ $r3 = 0 ] || fail "$f: official $r1, exact $r2, reuse $r3: $(cat $f.reuse.out)"
      cmp -s $f.exact.olean $f.reuse.olean || fail "$f: the .olean differs from a run that reuses nothing"
      grep -q "t2 : chooseProp% → True\|t2 : True → True\|t2 : False → True" $f.official.out ||
        fail "$f: does not test what it should: $(cat $f.official.out)"
    fi
    $DIFF -- $f.official.out $f.exact.out || fail "$f: the output of exact differs from official Lean's"
    $DIFF -- $f.official.out $f.reuse.out || fail "$f: the output of reuse differs from official Lean's"
    # (the reason is the fallback's report; the reuse must not have happened behind it)
    grep -q "$why" $f$v.stats || fail "$f: the statistics do not say why: $(cat $f$v.stats)"
    awk -F '\t' '$6 == 0' $f$v.stats | grep -q . || fail "$f: reused its variables: $(cat $f$v.stats)"
  done
}

READS="not on the whitelist"

elaborator "env.contains \`marker" 1000 Contains
check Contains Contains "def marker := 1" "$READS"

elaborator "env.contains \`marker" 100 Contains100
check Contains100 Contains100 "def marker := 1" "$READS"

elaborator "(env.find? \`marker).isSome" 100 Find
check Find Find "def marker := 1" "$READS"

elaborator "isClass env \`D" 100 Class
check Class Class "class D where" "$READS"

elaborator "isInstanceCore env \`marker" 100 Instance
check Instance Instance "@[instance] def marker : Inhabited Nat := ⟨0⟩" "$READS"

elaborator "getReducibilityStatusCore env \`marker == .reducible" 100 Reducible
check Reducible Reducible "@[reducible] def marker := 1" "$READS"

elaborator "env.isNamespace \`marker" 100 Ns
check Ns Ns "namespace marker
def a := 1
end marker" "$READS"

elaborator "env.constants.map₂.toList.any (·.1 == \`marker)" 100 Constants
check Constants Constants "def marker := 1" "$READS"

# a helper of another module, called by an elaborator compiled as usual
cat > Inner.lean <<'EOF'
import Lean
set_option compiler.small 100
def Inner.hasMarker (env : Lean.Environment) : Bool := env.contains `marker
EOF
official -o lib/Inner.olean Inner.lean > build.out 2>&1 || fail "Inner.lean: $(cat build.out)"
cat > Outer.lean <<'EOF'
import Inner
open Lean Elab Term
elab "chooseProp%" : term => do
  return mkConst (if Inner.hasMarker (← getEnv) then ``False else ``True)
EOF
official -o lib/Outer.olean Outer.lean > build.out 2>&1 || fail "Outer.lean: $(cat build.out)"
check Transitive Outer "def marker := 1" "$READS"

# a closure in a reference made by `initialize`, which nothing but the initializer leads to
cat > Handler.lean <<'EOF'
import Lean
open Lean Elab Term
set_option compiler.small 100
initialize chooser : IO.Ref (Environment → Bool) ← IO.mkRef fun env => env.contains `marker
elab "chooseProp%" : term => do
  let f ← chooser.get
  return mkConst (if f (← getEnv) then ``False else ``True)
EOF
official -o lib/Handler.olean Handler.lean > build.out 2>&1 || fail "Handler.lean: $(cat build.out)"
check Handler Handler "def marker := 1" "$READS"

# a closure that an extension gets by evaluating a name when a module is imported
cat > Table.lean <<'EOF'
import Lean
open Lean Elab Term
def Chooser := Environment → Bool
set_option compiler.small 100 in
def Chooser.impl : Chooser := fun env => env.contains `marker
initialize chooserExt : PersistentEnvExtension Unit Unit (Option Chooser) ←
  registerPersistentEnvExtension {
    mkInitial := pure none
    addImportedFn := fun _ => do
      let ctx ← read
      return (unsafe ctx.env.evalConstCheck Chooser ctx.opts ``Chooser ``Chooser.impl).toOption
    addEntryFn := fun s _ => s
    exportEntriesFn := fun _ => #[]
  }
elab "chooseProp%" : term => do
  let env ← getEnv
  let some f := chooserExt.getState env | return mkConst ``True
  return mkConst (if f env then ``False else ``True)
EOF
official -o lib/Table.olean Table.lean > build.out 2>&1 || fail "Table.lean: $(cat build.out)"
check Table Table "def marker := 1" "$READS"

# the code of the second elaborator of a recording, after one that reads nothing
cat > TwoElabs.lean <<'EOF'
import Lean
open Lean Elab Term
elab "firstProp%" : term => return mkConst ``True
set_option compiler.small 100 in
elab "secondProp%" : term => do
  return mkConst (if (← getEnv).contains `marker then ``False else ``True)
macro "chooseProp%" : term => `(firstProp% ∧ secondProp%)
EOF
official -o lib/TwoElabs.olean TwoElabs.lean > build.out 2>&1 || fail "TwoElabs.lean: $(cat build.out)"
cat > TwoMain.lean <<'EOF'
import TwoElabs
variable (a : firstProp%) (h : secondProp%)
include a h
theorem t1 : True := h
theorem t2 : True := h
def marker := 1
theorem t3 : True := h
EOF
set +e
official TwoMain.lean > two.official.out 2>&1; r1=$?
PAPERLEAN_REUSE=1 lean TwoMain.lean > two.reuse.out 2>&1; r2=$?
set -e
[ $r1 = 1 ] || fail "TwoMain.lean: official Lean does not reject the file: $(cat two.official.out)"
[ $r2 = 1 ] || fail "TwoMain.lean: a file that official Lean rejects, reuse $r2: $(cat two.reuse.out)"
$DIFF -- two.official.out two.reuse.out || fail "TwoMain.lean: the output differs from official Lean's"

# polymorphic code, in a closure
cat > Poly.lean <<'EOF'
import Lean
open Lean Elab Term
set_option compiler.small 100
@[noinline] def Poly.check [Monad m] [MonadEnv m] (k : Bool → m α) : m α := do
  k ((← getEnv).contains `marker)
elab "chooseProp%" : term => Poly.check fun b => return mkConst (if b then ``False else ``True)
EOF
official -o lib/Poly.olean Poly.lean > build.out 2>&1 || fail "Poly.lean: $(cat build.out)"
check Poly Poly "def marker := 1" "$READS"

# an elaborator of the file itself that calls the inlined helper
for v in Rejected Accepted; do
  {
    cat <<'EOF'
import Inner
open Lean Elab Term
elab "localProp%" : term => return mkConst (if Inner.hasMarker (← getEnv) then ``False else ``True)
variable (h : localProp%)
include h
theorem t1 : True := h
theorem t2 : True := h
EOF
    if [ $v = Rejected ]; then echo "def marker := 1"; fi
    echo "theorem t3 : True := h"
  } > Local$v.lean
  set +e
  official Local$v.lean > local.official.out 2>&1; r1=$?
  PAPERLEAN_REUSE=1 PAPERLEAN_REUSE_STATS=Local$v.stats lean Local$v.lean > local.reuse.out 2>&1; r2=$?
  set -e
  [ $r1 = $r2 ] || fail "Local$v.lean: official $r1, reuse $r2: $(cat local.reuse.out)"
  $DIFF -- local.official.out local.reuse.out || fail "Local$v.lean: the output differs from official Lean's"
  if [ $v = Rejected ]; then [ $r1 = 1 ] || fail "Local$v.lean: official Lean does not reject it"; fi
  awk -F '\t' '$6 == 0' Local$v.stats | grep -q . || fail "Local$v.lean reused its variables: $(cat Local$v.stats)"
done

# a `module`, whose code an import does not load, and which can inline Lean's functions only with
# `import all` of their module; also imported by a `module`, as in a build (`--setup`), which does not
# load the part that has the code
cat > Mod.lean <<'EOF'
module
public meta import Lean
meta import all Lean.Environment
open Lean Elab Term
set_option compiler.small 100
public meta section
syntax (name := chooseProp) "chooseProp%" : term
@[term_elab chooseProp] def elabChooseProp : TermElab := fun _ _ => do
  let env ← getEnv
  return mkConst (if env.contains `marker then ``False else ``True)
end
EOF
official -o lib/Mod.olean Mod.lean > build.out 2>&1 || fail "Mod.lean: $(cat build.out)"
[ -f lib/Mod.olean.private ] || fail "Mod.lean does not test what it should: no private part"
check ModuleFile Mod "def marker := 1" "$READS"
cat > ModMain.lean <<'EOF'
module
public meta import Mod
public section
variable (h : chooseProp%)
include h
theorem t1 : True := h
theorem t2 : True := h
def marker := 1
theorem t3 : True := h
EOF
cat > ModMain.json <<'EOF'
{"name":"ModMain","package":null,"isModule":true,"options":{},"plugins":[],"dynlibs":[],"importArts":{}}
EOF
set +e
official --setup ModMain.json ModMain.lean > mod_main.official.out 2>&1; r1=$?
PAPERLEAN_REUSE=1 PAPERLEAN_REUSE_STATS=mod_main.stats lean --setup ModMain.json ModMain.lean \
  > mod_main.reuse.out 2>&1; r2=$?
set -e
[ $r1 = 1 ] && [ $r2 = 1 ] || fail "ModMain.lean: official $r1, reuse $r2: $(cat mod_main.reuse.out)"
$DIFF -- mod_main.official.out mod_main.reuse.out || fail "ModMain.lean: the output differs from official Lean's"
grep -q "$READS" mod_main.stats || fail "ModMain.lean does not say why: $(cat mod_main.stats)"

# code that Lean's own functions run, in a table that no name of a recording leads to: a simproc is
# evaluated when its module is imported
cat > Simproc.lean <<'EOF'
import Lean
open Lean Meta Elab Term
def chooseConst : Prop := True
set_option compiler.small 100 in
simproc chooseSimproc (chooseConst) := fun _ => do
  return if (← getEnv).contains `marker then .done { expr := mkConst ``False } else .continue
elab "chooseProp%" : term => do
  let (r, _) ← simp (mkConst ``chooseConst) (← Simp.mkContext) #[← Simp.getSimprocs]
  return mkConst (if r.expr.isFalse then ``False else ``True)
EOF
official -o lib/Simproc.olean Simproc.lean > build.out 2>&1 || fail "Simproc.lean: $(cat build.out)"
check Simproc Simproc "def marker := 1" "$READS"

cat > Dsimproc.lean <<'EOF'
import Lean
open Lean Meta Elab Term
def chooseConst : Prop := True
set_option compiler.small 100 in
dsimproc chooseDsimproc (chooseConst) := fun _ => do
  return if (← getEnv).contains `marker then .done (mkConst ``False) else .continue
elab "chooseProp%" : term => do
  let (e, _) ← dsimp (mkConst ``chooseConst) (← Simp.mkContext) #[← Simp.getSimprocs]
  return mkConst (if e.isFalse then ``False else ``True)
EOF
official -o lib/Dsimproc.olean Dsimproc.lean > build.out 2>&1 || fail "Dsimproc.lean: $(cat build.out)"
check Dsimproc Dsimproc "def marker := 1" "$READS"

cat > CbvProc.lean <<'EOF'
import Lean
open Lean Meta Elab Term
opaque chooseConst : Nat
set_option compiler.small 100 in
cbv_simproc chooseCbv (chooseConst) := fun _ => do
  if (← getEnv).contains `marker then throwError "marked"
  return .rfl
elab "chooseProp%" : term => do
  try
    discard <| Lean.Meta.Tactic.Cbv.cbvEntry (mkConst ``chooseConst)
    return mkConst ``True
  catch _ => return mkConst ``False
EOF
official -o lib/CbvProc.olean CbvProc.lean > build.out 2>&1 || fail "CbvProc.lean: $(cat build.out)"
check CbvProc CbvProc "def marker := 1" "$READS"

# ... whose dispatch official Lean may have inlined into an elaborator
sed -e '/^elab/,$d' Simproc.lean > Dispatch.lean
cat >> Dispatch.lean <<'EOF'
set_option compiler.small 100 in
@[noinline] def dispatch (s : Simprocs) : SimpM Simp.Step :=
  Simp.simprocCore true s.post s.erased (mkConst ``chooseConst)
elab "chooseProp%" : term => do
  let (step, _) ← (dispatch (← Simp.getSimprocs)).run (← Simp.mkContext)
  let isFalse := match step with
    | .done r => r.expr.isFalse
    | _ => false
  return mkConst (if isFalse then ``False else ``True)
EOF
official -o lib/Dispatch.olean Dispatch.lean > build.out 2>&1 || fail "Dispatch.lean: $(cat build.out)"
check Dispatch Dispatch "def marker := 1" "$READS"

# ... or that an elaborator runs itself
sed -e '/^elab/,$d' Simproc.lean > EntryTry.lean
cat >> EntryTry.lean <<'EOF'
def tryAll (s : Simprocs) (e : Expr) : SimpM Bool := do
  for (entry, n) in ← s.post.getMatchWithExtra e do
    if let .done r ← entry.try n e then
      return r.expr.isFalse
  return false
elab "chooseProp%" : term => do
  let (marked, _) ← (tryAll (← Simp.getSimprocs) (mkConst ``chooseConst)).run (← Simp.mkContext)
  return mkConst (if marked then ``False else ``True)
EOF
official -o lib/EntryTry.olean EntryTry.lean > build.out 2>&1 || fail "EntryTry.lean: $(cat build.out)"
check EntryTry EntryTry "def marker := 1" "$READS"

# ... and tactics, which are not recorded at all
sed -e '/^elab/,$d' Simproc.lean > SimprocOnly.lean
cat >> SimprocOnly.lean <<'EOF'
macro "chooseProp%" : term =>
  `((by first | (have : chooseConst = False := by simp); exact False | exact True : Prop))
EOF
official -o lib/SimprocOnly.olean SimprocOnly.lean > build.out 2>&1 ||
  fail "SimprocOnly.lean: $(cat build.out)"
check BinderTactic SimprocOnly "def marker := 1" "a tactic"

# ... and functions that an `initialize` adds to a table of Lean's
cat > EqnsFn.lean <<'EOF'
import Lean
open Lean Meta Elab Term
def probe : Nat := 0
set_option compiler.small 100 in
initialize registerGetEqnsFn fun n => do
  if n == ``probe then throwError (if (← getEnv).contains `marker then "marked" else "not marked")
  return none
elab "chooseProp%" : term => do
  try
    discard <| getEqnsFor? ``probe
    return mkConst ``True
  catch e =>
    return mkConst (if (← e.toMessageData.toString) == "marked" then ``False else ``True)
EOF
official -o lib/EqnsFn.olean EqnsFn.lean > build.out 2>&1 || fail "EqnsFn.lean: $(cat build.out)"
check EqnsFn EqnsFn "def marker := 1" "$READS"

cat > UnfoldFn.lean <<'EOF'
import Lean
open Lean Meta Elab Term
def probe : Nat → Nat
  | 0 => 0
  | n + 1 => probe n
set_option compiler.small 100 in
initialize registerGetUnfoldEqnFn fun n => do
  if n == ``probe then throwError (if (← getEnv).contains `marker then "marked" else "not marked")
  return none
elab "chooseProp%" : term => do
  try
    discard <| getUnfoldEqnFor? ``probe
    return mkConst ``True
  catch e =>
    return mkConst (if (← e.toMessageData.toString) == "marked" then ``False else ``True)
EOF
official -o lib/UnfoldFn.olean UnfoldFn.lean > build.out 2>&1 || fail "UnfoldFn.lean: $(cat build.out)"
check UnfoldFn UnfoldFn "def marker := 1" "$READS"

cat > ActionFn.lean <<'EOF'
import Lean
open Lean Meta Elab Term
set_option compiler.small 100 in
initialize registerReservedNameAction fun n => do
  if n == `probe then throwError (if (← getEnv).contains `marker then "marked" else "not marked")
  return false
elab "chooseProp%" : term => do
  try
    executeReservedNameAction `probe
    return mkConst ``True
  catch e =>
    return mkConst (if (← e.toMessageData.toString) == "marked" then ``False else ``True)
EOF
official -o lib/ActionFn.olean ActionFn.lean > build.out 2>&1 || fail "ActionFn.lean: $(cat build.out)"
check ActionFn ActionFn "def marker := 1" "$READS"

# (the solvers of `grind` and the extensions of `Sym`, whose functions run in the goals of a search:
# here the read of their table, which a change of the environment does not reach; and an elaborator
# that runs a tactic itself, whose tables of Lean's are all of those above and more)
cat > ExtFn.lean <<'EOF'
import Lean
open Lean Meta Elab Term
initialize solver : Grind.SolverExtension Unit ← Grind.registerSolverExtension (pure ())
initialize symExt : Sym.SymExtension Unit ← Sym.registerSymExtension (pure ())
initialize Grind.registerBuiltinUpwardPropagator `probe fun _ => pure ()
elab "solverProp%" : term => do
  discard <| Grind.Solvers.mkInitialStates
  return mkConst ``True
elab "symProp%" : term => do
  discard <| Sym.SymExtensions.mkInitialStates
  return mkConst ``True
elab "propagatorProp%" : term => do
  discard <| Grind.builtinPropagatorsRef.get
  return mkConst ``True
elab "tacticProp%" : term => do
  let goal ← mkFreshExprMVar (mkConst ``True)
  (← Tactic.run goal.mvarId! (pure ())).forM (·.admit)
  return mkConst ``True
EOF
official -o lib/ExtFn.olean ExtFn.lean > build.out 2>&1 || fail "ExtFn.lean: $(cat build.out)"
for p in solverProp% symProp% propagatorProp% tacticProp%; do
  cat > ExtMain.lean <<EOF
import ExtFn
variable (h : $p)
include h
theorem t1 : True := h
theorem t2 : True := h
EOF
  rm -f ext.stats
  PAPERLEAN_REUSE=1 PAPERLEAN_REUSE_STATS=ext.stats lean -DmaxRecDepth=0 ExtMain.lean > ext.out 2>&1 ||
    fail "ExtMain.lean with $p: $(cat ext.out)"
  grep -q "$READS" ext.stats || fail "$p: the statistics do not say why: $(cat ext.stats)"
  awk -F '\t' '$6 == 0' ext.stats | grep -q . || fail "$p: reused its variables: $(cat ext.stats)"
done

# compiled as usual, with the same result
elaborator "env.contains \`marker" 1 Usual
check Usual Usual "def marker := 1" "$READS"

# the summary of `paperlean build` says it
mkdir -p ws/.lake/build/lib/lean
cp lib/Contains.olean ws/.lake/build/lib/lean/
cd ws
cat > lakefile.toml <<'END'
name = "root"
defaultTargets = ["Root"]
[[lean_lib]]
name = "Root"
END
cat > Root.lean <<'EOF'
import Contains
variable (h : chooseProp%)
include h
theorem t1 : True := h
theorem t2 : True := h
theorem t3 : True := h
EOF
capture lake paperlean build
grep -Eq "^  3 section variables: not recordable: the elaborator .*ChooseProp.*, not on the whitelist \(Root\.lean:[0-9]+:[0-9]+\)$" "$CAPTURED.out.produced" ||
  fail "the summary does not say why: $(cat "$CAPTURED.out.produced")"
