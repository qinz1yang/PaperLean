# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that PaperLean counts no more heartbeats than official Lean 4.35.0-rc3 where its typeclass
# cache records what Lean's search reads and what it does to Lean's caches, and where it reuses
# section variables: with limits under which official Lean succeeds (a search of a 30-step instance
# chain under `synthInstance.maxHeartbeats 19`, the declaration under `maxHeartbeats 49`, section
# variables that need it under `maxHeartbeats 82`, the least with which official Lean succeeds),
# PaperLean succeeds too, and the search counts
# at most official Lean's 19190 heartbeats. Also in the compiler: compiling, in a non-module file, a
# definition that calls `Array.contains` on strings, which reuses a specialization of the toolchain
# (`Specialize.findSpecCache?`), counts at most official Lean's 6147 heartbeats; and in a `module`,
# compiling the identity on `Nat` (with the interpreter's first call of `compileDecl`) counts at most
# official Lean's 2776.
# And that registering 100 macros counts at most official Lean's 7472. (The bounds are official
# rc3's numbers on these files.)

export PAPERLEAN_REUSE=1

cd "$TMP_DIR"
{
  for i in $(seq 0 30); do echo "class C$i (α : Type) where"; done
  for i in $(seq 1 30); do echo "instance [C$((i - 1)) α] : C$i α := ⟨⟩"; done
  for i in $(seq 0 30); do echo "instance [C$i α] : C$i (Option α) := ⟨⟩"; done
  echo "instance : C0 Nat := ⟨⟩"
} > Chain.lean
{ cat Chain.lean; echo "set_option synthInstance.maxHeartbeats 19 in"
  echo "example : C30 (Option (Option Nat)) := inferInstance"; } > Limit.lean
{ cat Chain.lean; echo "set_option maxHeartbeats 49 in"
  echo "example : C30 (Option (Option Nat)) := inferInstance"; } > Decl.lean
{ cat Chain.lean; echo "def P (α : Type) [C30 α] : Prop := True"
  echo "variable (h1 : P (Option (Option Nat))) (h2 : P (Option Nat)) (h3 : P Nat)"
  echo "  (h4 : P (Option (Option (Option Nat))))"
  echo "include h1 h2 h3 h4"
  echo "set_option maxHeartbeats 82 in"
  echo "theorem t : True := trivial"; } > SecVars.lean
for f in Limit Decl SecVars; do
  lean $f.lean > $f.out 2>&1 || fail "$f.lean failed where official Lean succeeds: $(cat $f.out)"
  if grep -q "heartbeats" $f.out; then fail "$f.lean: $(cat $f.out)"; fi
done
{ echo "import Lean"; echo "open Lean Meta"; cat Chain.lean
  echo 'def hb (e : Expr) : MetaM Unit := do'
  echo '  let h0 ← IO.getNumHeartbeats'
  echo '  discard <| synthInstance e'
  echo '  let h1 ← IO.getNumHeartbeats'
  echo '  logInfo m!"heartbeats {h1 - h0}"'
  echo 'run_meta hb (mkApp (mkConst ``C30) (mkApp (mkConst ``Option [0]) (mkApp (mkConst ``Option [0]) (mkConst ``Nat))))'
} > Count.lean
lean Count.lean > count.out 2>&1 || fail "Count.lean failed: $(cat count.out)"
N=$(sed -n 's/^heartbeats \([0-9]*\)$/\1/p' count.out)
[ -n "$N" ] && [ "$N" -le 19190 ] || fail "the search counts more heartbeats than official Lean's 19190: $(cat count.out)"
cat > CompileHb.lean <<'EOF2'
import Lean
open Lean Elab Command Term Meta
set_option Elab.async false
elab "#compile_hb" : command => liftTermElabM do
  let e ← elabTerm (← `(fun (a : Array String) (s : String) => a.contains s)) none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let decl := Declaration.defnDecl
    { name := `g, levelParams := [], type := ← inferType e, value := e, hints := .abbrev, safety := .safe }
  addDecl decl
  let h0 ← IO.getNumHeartbeats
  compileDecl decl
  let h1 ← IO.getNumHeartbeats
  logInfo m!"heartbeats {h1 - h0}"
#compile_hb
EOF2
lean CompileHb.lean > compile.out 2>&1 || fail "CompileHb.lean failed: $(cat compile.out)"
N=$(sed -n 's/^heartbeats \([0-9]*\)$/\1/p' compile.out)
[ -n "$N" ] && [ "$N" -le 6147 ] ||
  fail "compiling counts more heartbeats than official Lean's 6147: $(cat compile.out)"
cat > CompileHbModule.lean <<'EOF2'
module
public import Lean
open Lean Elab Command Term Meta
set_option Elab.async false
elab "#compile_hb" : command => liftTermElabM do
  let e ← elabTerm (← `(fun (n : Nat) => n)) none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let decl := Declaration.defnDecl
    { name := `g, levelParams := [], type := ← inferType e, value := e, hints := .abbrev, safety := .safe }
  addDecl decl
  let h0 ← IO.getNumHeartbeats
  compileDecl decl
  let h1 ← IO.getNumHeartbeats
  logInfo m!"heartbeats {h1 - h0}"
#compile_hb
EOF2
lean CompileHbModule.lean > compile_module.out 2>&1 ||
  fail "CompileHbModule.lean failed: $(cat compile_module.out)"
N=$(sed -n 's/^heartbeats \([0-9]*\)$/\1/p' compile_module.out)
[ -n "$N" ] && [ "$N" -le 2776 ] ||
  fail "compiling in a module counts more heartbeats than official Lean's 2776: $(cat compile_module.out)"
# registering 100 macros counts at most official Lean's 7472 (`PAPERLEAN_EXACT=1` registers the same)
{
  echo "import Lean"
  echo "open Lean Elab Command"
  echo 'syntax (name := fooK) "foo%" : term'
  for i in $(seq 0 99); do echo "def fooMacro$i : Macro := fun _ => pure (Syntax.mkNumLit \"0\")"; done
  cat <<'EOF2'
run_cmd do
  let .ok a := getAttributeImpl (← getEnv) `macro | throwError "attribute missing"
  let .ok s := Parser.runParserCategory (← getEnv) `attr "macro fooK" | throwError "parse"
  let h0 ← IO.getNumHeartbeats
  for i in [:100] do
    liftCoreM <| a.add (Name.mkSimple ("fooMacro" ++ toString i)) s .global
  let h1 ← IO.getNumHeartbeats
  logInfo m!"heartbeats {h1 - h0}"
EOF2
} > ProvHb.lean
for mode in "" "PAPERLEAN_EXACT=1"; do
  env $mode lean ProvHb.lean > provhb.out 2>&1 || fail "ProvHb.lean failed ($mode): $(cat provhb.out)"
  N=$(sed -n 's/^heartbeats \([0-9]*\)$/\1/p' provhb.out)
  [ -n "$N" ] && [ "$N" -le 7472 ] ||
    fail "registering macros counts more heartbeats than official Lean's 7472 ($mode): $(cat provhb.out)"
done
# PaperLean's own bookkeeping counts none (the bound of `Count.lean` above could not tell, being official
# Lean's): the read of whether realizations are enabled for a constant, for an imported one, for one of
# the module with them and one without, each with a thread that records and one that does not.
cat > RealizationsRead.lean <<'EOF2'
module
import all Lean.Meta.FunInfo
import Lean
open Lean Meta Elab
class LocalClass where
def probe (env : Environment) (n : Name) : BaseIO (Bool × Nat) := do
  let heartbeats ← IO.getNumHeartbeats
  let enabled ← realizationsEnabled env n
  let after ← IO.getNumHeartbeats
  return (enabled, after - heartbeats)
run_meta do
  addDecl <| .axiomDecl { name := `NotEnabled, levelParams := [], type := mkSort 1, isUnsafe := false }
  let env ← getEnv
  for n in [``Nat, ``LocalClass, `NotEnabled] do
    let (enabled, counted) ← probe env n
    logInfo m!"{n} enabled={enabled} counted={counted}"
    PaperLean.envStartRecording
    let (enabled, counted) ← probe env n
    discard PaperLean.envStopRecording
    logInfo m!"{n} recording enabled={enabled} counted={counted}"
EOF2
lean RealizationsRead.lean > read.out 2>&1 || fail "RealizationsRead.lean failed: $(cat read.out)"
[ "$(grep -c "enabled=true counted=" read.out)" = 4 ] && [ "$(grep -c "enabled=false counted=" read.out)" = 2 ] ||
  fail "RealizationsRead.lean does not test what it should: $(cat read.out)"
! grep "counted=" read.out | grep -v "counted=0$" || fail "the bookkeeping counted heartbeats: $(cat read.out)"
# ... and a search through Lean's `getFunInfo` of imported constants, recorded: 494 is what it counts
# itself (official Lean's 573 less what PaperLean's recording leaves out, and no bookkeeping).
cat > RecordedSearch.lean <<'EOF2'
import Lean
open Lean Meta Elab
class D (α : Type) where
instance : D (List α) := ⟨⟩
run_meta do
  let ty := mkApp (mkConst ``D) (mkApp (mkConst ``List [Level.zero]) (mkConst ``Nat))
  let h ← IO.getNumHeartbeats
  let _ ← synthInstance ty
  let h' ← IO.getNumHeartbeats
  logInfo m!"search heartbeats: {h' - h}"
EOF2
lean RecordedSearch.lean > recorded.out 2>&1 || fail "RecordedSearch.lean failed: $(cat recorded.out)"
N=$(sed -n 's/^search heartbeats: \([0-9]*\)$/\1/p' recorded.out)
[ -n "$N" ] && [ "$N" -le 494 ] || fail "a recorded search counts more than its own 494 heartbeats: $(cat recorded.out)"
# ... and the recording of what Lean's functions read and do to their caches: the path of a thread that
# records counts no more than the plain one, on what each of the hooks passes through. (On a hit of a
# cache too, where a record that held the result of the lookup would keep Lean from reusing that object
# for its own result, so that it counts another, as `whnf` of a type in a telescope would show, and
# `getFunInfo`, which does that.)
cat > RecordingPaths.lean <<'EOF2'
import Lean
open Lean Meta Elab
class Cl (α : Type) where
instance : Cl Nat := ⟨⟩
@[reducible] def locR := Nat
theorem locT : True := trivial
/-- The heartbeats of the second run of `act` from empty caches of `MetaM`: the first one fills `CoreM`'s. -/
def probe (act : MetaM Unit) (recording : Bool) : MetaM Nat := do
  modify ({ · with cache := {} }); act
  modify ({ · with cache := {} })
  if recording then PaperLean.envStartRecording
  let h ← IO.getNumHeartbeats
  act
  let h' ← IO.getNumHeartbeats
  if recording then discard PaperLean.envStopRecording
  return h' - h
def row (name : String) (act : MetaM Unit) : MetaM Unit := do
  let mut plain := #[]
  let mut recording := #[]
  for _ in [0:5] do
    plain := plain.push (← probe act false)
    recording := recording.push (← probe act true)
  let p := plain.foldl min plain[0]!
  let r := recording.foldl min recording[0]!
  logInfo m!"{name}: {if r ≤ p then "same" else "more"} plain {p} recording {r}"
run_meta do
  let env ← getEnv
  let nat := mkConst ``Nat
  let fn := mkForall `n .default nat nat
  row "find?" (discard <| pure (env.find? ``Nat.add))
  row "find? local" (discard <| pure (env.find? ``locT))
  row "getConstInfo" (discard <| getConstInfo ``Nat.add)
  row "isInstance" (discard <| isInstance ``Nat.add)
  row "getReducibilityStatus" (discard <| getReducibilityStatus ``locR)
  row "isClass?" (discard <| isClass? nat)
  row "getUnfoldableConst?" (discard <| getUnfoldableConst? ``locR)
  row "resolveGlobalName" (discard <| resolveGlobalName `Nat.add)
  row "resolveNamespace" (discard <| pure (ResolveName.resolveNamespace env `x [] `Nat))
  row "synthInstance" (discard <| synthInstance (mkApp (mkConst ``Cl) nat))
  row "unfoldDefinition?" (discard <| unfoldDefinition? (mkApp2 (mkConst ``Nat.add) (mkNatLit 1) (mkNatLit 2)))
  row "whnf" (discard <| whnf (mkApp2 (mkConst ``Nat.add) (mkNatLit 1) (mkNatLit 2)))
  row "whnf, misses" (do discard <| whnf (mkApp (mkConst ``List [0]) nat); discard <| whnf nat)
  row "whnf, a hit" (do discard <| whnf nat; discard <| whnf nat)
  row "whnf, two hits" (do discard <| whnf nat; discard <| whnf nat; discard <| whnf nat)
  row "inferType, a hit" (do let t := mkApp (mkConst ``List [0]) nat; discard <| inferType t; discard <| inferType t)
  row "getFunInfo, a hit" (do discard <| getFunInfo nat; discard <| getFunInfo nat)
  row "getFunInfo imported" (discard <| getFunInfo (mkConst ``Nat.add))
  row "getFunInfo local" (discard <| getFunInfo (mkConst ``locT))
  row "inferType local" (discard <| inferType (mkConst ``locT))
  row "getFunInfo lambda" (discard <| getFunInfo (mkLambda `x .default nat (.bvar 0)))
  row "getFunInfo mvar" (do discard <| getFunInfo (← mkFreshExprMVar fn))
  withLocalDeclD `f fn fun f => withLocalDeclD `n nat fun n => do
    row "inferType" (discard <| inferType (mkApp f n))
    row "isDefEq" (discard <| isDefEq (mkApp f n) (mkApp f n))
    row "forallTelescopeReducing" (forallBoundedTelescope fn none fun xs _ => do
      discard <| forallTelescopeReducing (← inferType xs[0]!) fun _ t => return t.isAppOf ``Decidable)
    row "getFunInfo fvar" (discard <| getFunInfo f)
EOF2
env -u PAPERLEAN_REUSE lean RecordingPaths.lean > paths.out 2>&1 || fail "RecordingPaths.lean failed: $(cat paths.out)"
[ "$(grep -c " plain [0-9]* recording [0-9]*$" paths.out)" = 26 ] ||
  fail "RecordingPaths.lean does not test what it should: $(cat paths.out)"
! grep -q ": more plain" paths.out || fail "a thread that records counts more: $(grep ": more plain" paths.out)"
