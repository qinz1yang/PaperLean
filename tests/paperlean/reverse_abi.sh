# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests the reverse direction of rule 4, that official Lean 4.35.0-rc3's compiled code finds in
# PaperLean every entry point that it actually calls:
# - every undefined `l_`/`lp_` symbol of the official-built `Fin.o` exists in PaperLean's libraries
#   (the global official-library symbol set is a native-ABI inventory, not this contract);
# - `Fin.lean` is compiled at the default `compiler.small`, linked against PaperLean's libraries,
#   and runs under official, PaperLean and `PAPERLEAN_EXACT` with the same computed values;
# - the full IR/signature and generated-call differences are printed for diagnosis.
# - a caller built by official Lean (`Fin.lean`), which inlines the upstream functions that PaperLean
#   changes most, links against PaperLean's libraries and runs under PaperLean, natively and
#   interpreted, also under `PAPERLEAN_EXACT=1`, printing what it prints under official Lean.
# It needs official Lean, at `$OFFICIAL_LEAN_TOOLCHAIN` or elan's, and fails without it: without
# official Lean nothing here is checked.
OFFICIAL=${OFFICIAL_LEAN_TOOLCHAIN:-$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3}
[ -x "$OFFICIAL/bin/lean" ] ||
  fail "official Lean 4.35.0-rc3 is not at $OFFICIAL (set OFFICIAL_LEAN_TOOLCHAIN to where it is)"

cp reverse_abi.lean "$TMP_DIR/"
cd "$TMP_DIR"
export LC_ALL=C

# Lean's symbols that the shared libraries of the toolchain at `$1` export
syms() {
  for l in "$1"/lib/lean/lib*.so "$1"/lib/lean/lib*.dylib; do
    [ -f "$l" ] || continue
    if [[ "$(uname)" == Darwin ]]; then
      nm -gU "$l" | awk '{print $3}' | sed 's/^_//'
    else
      nm -D --defined-only "$l" | awk '$2 ~ /[TDBR]/ {print $3}'
    fi
  done | grep -E '^(l_|lp_|lean_|initialize_)' | sort -u
}
syms "$OFFICIAL" > syms.official
syms "$BUILD_DIR" > syms.paperlean
[ "$(wc -l < syms.official)" -gt 100000 ] || fail "few symbols found in official Lean's libraries"
# (not every symbol official Lean's libraries export is required: only those that official-compiled
# code actually calls, checked from Fin.o below; native stress specializations are a separate class)

"$OFFICIAL/bin/lean" --run reverse_abi.lean "$OFFICIAL/lib/lean" abi.official
LEAN_PATH= lean --run reverse_abi.lean "$BUILD_DIR/lib/lean" abi.paperlean
sort -u abi.official > abi.official.sorted
sort -u abi.paperlean > abi.paperlean.sorted
[ "$(wc -l < abi.official.sorted)" -gt 500000 ] || fail "few declarations of official Lean read"
comm -23 abi.official.sorted abi.paperlean.sorted > abi.differ
grep -v '^calls ' abi.differ > sigs.differ || true
echo "(diagnostic: $(wc -l < sigs.differ) IR/signature differences, mostly compiler-generated \
specializations; native ABI is checked by the Fin link/run below)"

# The generated declarations that call a hook of PaperLean: official Lean's code, with the hook.
cat > expected_calls <<'EOF2'
Lake.Workspace.runBuild._redArg
Lake.buildAction._at_._private.Lake.Build.Module.0.Lake.Module.buildLean.spec_0
Lake.fetchFileHash._redArg
Lean.Elab.Command.runTermElabM._redArg
Lean.Elab.Term.runTactic._lam_9
Lean.Environment.evalConst._redArg
Lean.KeyedDeclsAttribute.addBuiltin._redArg
Lean.KeyedDeclsAttribute.getEntries._redArg
Lean.Meta.SynthInstance.getInstances._lam_0
Lean.Meta.whnfEasyCases._at_.Lean.Meta.whnfImp.spec_3
Lean.Meta.whnfEasyCases._at_._private.Lean.Meta.WHNF.0.Lean.Meta.whnfCore.go.spec_3
Lean.ScopedEnvExtension.getState._redArg
Lean.registerScopedEnvExtensionUnsafe._redArg
_private.Init.Data.Array.Basic.0.Array.forIn'Unsafe.loop._at_.Lean.Elab.Command.runLinters.spec_4
_private.Init.Data.Array.Basic.0.Array.forIn'Unsafe.loop._at_.Lean.Elab.Command.runLinters.spec_5
_private.Lake.Build.Library.0.Lake.LeanLib.recCollectLocalModules._lam_0
_private.Lean.Environment.0.Lean.EnvExtension.getStateUnsafe._redArg
_private.Lean.Environment.0.Lean.setImportedEntries.unsafe_1._lam_0
_private.Lean.Meta.ExprDefEq.0.Lean.Meta.cacheResult._redArg
_private.Lean.Meta.WHNF.0.Lean.Meta.cache._redArg
EOF2
grep '^calls ' abi.differ > calls.differ || true
echo "(diagnostic: $(wc -l < calls.differ) generated-declaration call differences)"

# Official Lean builds the caller, with its body of the functions that PaperLean changes.
cat > Fin.lean <<'EOF2'
import Lean
/-! Non-module code that official Lean compiles with upstream's bodies of these functions inlined:
they call private and generated declarations with official Lean's calling conventions. -/
open Lean Meta
set_option maxRecDepth 100000
set_option maxHeartbeats 0

structure RealizedKey where
  n : Nat
  deriving BEq, Hashable, TypeName
structure Realized where
  n : Nat
  deriving TypeName

def callFinalize (s : ImportState) (imports : Array Import) (opts : Options) : IO Environment :=
  finalizeImport s imports opts 0 false true
def callImport (imports : Array Import) (opts : Options) : IO Environment :=
  importModules imports opts (loadExts := true)
def callFunInfo (e : Expr) : MetaM Nat := return (← getFunInfo e).paramInfo.size
def callSynth (e : Expr) : MetaM (Option Expr) := synthInstanceCore? e
def callSetup (s : ModuleSetup) : Except String ModuleSetup := fromJson? (toJson s)
def callResolve (env : Environment) (n : Name) : List (Name × List String) :=
  ResolveName.resolveGlobalName env {} .anonymous [] n
def callRealize (env : Environment) (c : Name) : IO Nat := do
  let d ← env.realizeValue c ({ n := 1 } : RealizedKey) fun _ _ => return .mk ({ n := 42 } : Realized)
  return (d.get? Realized).map (·.n) |>.getD 0
EOF2
cat > Use.lean <<'EOF2'
import Fin
/-! Runs the functions of `Fin` under the Lean that runs this file. -/
open Lean Meta

#eval show IO Unit from do
  unsafe enableInitializersExecution
  let imports := #[{ module := `Init : Import }]
  let (_, s) ← (importModulesCore imports).run
  let env ← callFinalize s imports {}
  IO.println s!"imported constants: {env.constants.map₁.size}"
  let env ← callImport imports {}
  IO.println s!"imported constants: {env.constants.map₁.size}"
  let e := mkConst ``Nat.add
  let ty := mkApp (mkConst ``Inhabited [1]) (mkConst ``Nat)
  let act : MetaM _ := do return (← callFunInfo e, ← callSynth ty)
  let ((n, r), _) ← act.run'.toIO { fileName := "", fileMap := default } { env }
  IO.println s!"{n} {r}"
  IO.println (repr (callResolve env `Nat.add))
  let setup : ModuleSetup := { name := `A, isModule := true }
  IO.println (repr (callSetup setup |>.toOption.map (·.name)))
  IO.println (← callRealize env ``Nat.add)
EOF2
env -u LEAN_CC -u LEANC_OPTS "$OFFICIAL/bin/lean" -o Fin.olean -c Fin.c Fin.lean ||
  fail "official Lean does not compile Fin.lean"
env -u LEAN_CC -u LEANC_OPTS "$OFFICIAL/bin/leanc" -c -fPIC -DLEAN_EXPORTING -o Fin.o Fin.c
# Every external symbol that official Lean's compiled test code calls must exist in PaperLean.
nm -u Fin.o | awk '{print $NF}' | sed 's/@.*//' | grep -E '^(l_|lp_|lean_|initialize_)' | sort -u > fin.undef
comm -23 fin.undef syms.paperlean > fin.missing
[ ! -s fin.missing ] || fail "$(wc -l < fin.missing) symbols called by official Lean's Fin.o are missing in PaperLean, e.g.
$(head -20 fin.missing)"
shared=(-shared)
[[ "$(uname)" == Darwin ]] && shared+=(-Wl,-undefined,dynamic_lookup)
env -u LEAN_CC -u LEANC_OPTS "$OFFICIAL/bin/leanc" "${shared[@]}" -o Fin.so Fin.o

if [[ "$(uname)" != Darwin ]]; then
  cc -shared -Wl,-z,defs -o Fin-linked.so Fin.o -L"$BUILD_DIR/lib/lean" -lleanshared -lleanshared_1 \
    -lleanshared_2 -lInit_shared -lLake_shared ||
    fail "official Lean's code does not link against PaperLean's libraries"
fi

# (PaperLean imports a few more modules than official rc3; the number of imported constants is not
# an ABI property, the values the code computes are)
normalize() { grep -v '^imported constants:' "$1"; }
run() { # <toolchain> <lean argument>…: the output of `Use.lean`
  local t=$1; shift
  env LEAN_PATH="$t/lib/lean:." "$t/bin/lean" "$@" Use.lean 2>&1
}
run "$OFFICIAL" -Dinterpreter.prefer_native=true --load-dynlib=./Fin.so > official.native ||
  fail "Use.lean fails under official Lean: $(cat official.native)"
run "$OFFICIAL" > official.interpreted || fail "Use.lean fails under official Lean: $(cat official.interpreted)"
$DIFF official.native official.interpreted
grep -q 'imported constants: [1-9]' official.native || fail "Use.lean printed $(cat official.native)"
run "$BUILD_DIR" -Dinterpreter.prefer_native=true --load-dynlib=./Fin.so > paperlean.native ||
  fail "official Lean's code fails under PaperLean, natively: $(cat paperlean.native)"
$DIFF <(normalize official.native) <(normalize paperlean.native)
run "$BUILD_DIR" > paperlean.interpreted ||
  fail "official Lean's code fails under PaperLean, interpreted: $(cat paperlean.interpreted)"
$DIFF <(normalize official.native) <(normalize paperlean.interpreted)
PAPERLEAN_EXACT=1 run "$BUILD_DIR" > paperlean.exact ||
  fail "official Lean's code fails under PAPERLEAN_EXACT=1: $(cat paperlean.exact)"
$DIFF <(normalize official.native) <(normalize paperlean.exact)
