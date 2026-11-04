# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests `paperlean prepare` where a module of a dependency has no `.olean`, as a killed build leaves
# it, outside what the root package imports: prepare finishes without trying to import the modules that
# import it (each such import fails, and once split the candidates down to single modules, every one
# importing its closure again), says which module is not built, and has the modules that import it,
# directly or not, run in the interpreter, the others natively; the results are those without native
# code, also after the module is built again.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN PAPERLEAN_DATA PAPERLEAN_EVAL_FAILED_IMPORTS
ROOT="$(cd "$TMP_DIR" && pwd -P)"
mkdir -p "$ROOT/dep/Dep" "$ROOT/ws/Root"
cd "$ROOT"
cat > dep/lakefile.toml <<'END'
name = "dep"
defaultTargets = ["Dep"]
[[lean_lib]]
name = "Dep"
END
printf 'def base : Nat := 1\n' > dep/Dep/Base.lean
printf 'def used : Nat := 41 + 1\n' > dep/Dep/Used.lean
{ echo 'import Dep.Used'
  for i in $(seq 1 24); do
    printf 'import Dep.Base\ndef mid%s : Nat := base + %s\n' $i $i > dep/Dep/Mid$i.lean
    printf 'import Dep.Mid%s\ndef top%s : Nat := mid%s * 2\n' $i $i $i > dep/Dep/Top$i.lean
    echo "import Dep.Top$i"
  done; } > dep/Dep.lean
cat > ws/lakefile.toml <<'END'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "dep"
path = "../dep"
[[lean_lib]]
name = "Root"
END
printf 'import Dep.Used\n#eval used\n' > ws/Root.lean
printf 'import Dep\n#eval used\n#eval mid3\n#eval top7\n' > ws/Use.lean
cd ws
run lake build Root Dep
capture lake lean Use.lean
cp "$CAPTURED.out.produced" "$TMP_DIR/plain.out"
OLEAN=../dep/.lake/build/lib/lean/Dep/Base.olean
rm "$OLEAN"

EVENTS="$TMP_DIR/events.txt"
capture env PAPERLEAN_EVAL_EVENTS="$EVENTS" lake paperlean prepare -j 2
check_out_contains "Prepared"
check_out_contains "modules of the dependencies import 1 modules that cannot be imported: Dep.Base is not built (its .olean file does not exist)."
# the modules that import it are not imported at all; the others are, together, once
! grep -q "^import-failed" "$EVENTS" || fail "an import of the modules to evaluate failed: $(grep '^import' "$EVENTS")"
[ "$(grep -c "^import	" "$EVENTS")" = 1 ] || fail "not one import of the modules to evaluate: $(grep '^import' "$EVENTS")"
for m in Mid3 Top7; do
  grep -q "^impure	.*/Dep/$m.olean	it imports Dep.Base, which is not built (its .olean file does not exist)$" "$EVENTS" ||
    fail "Dep.$m is not impure for importing Dep.Base: $(grep "/Dep/$m.olean" "$EVENTS")"
done
# (Dep.Mid<i>, Dep.Top<i> and Dep)
[ "$(grep -c "^impure	.*it imports Dep.Base" "$EVENTS")" = 49 ] || fail "not all 49 importers of Dep.Base are impure"
grep -q "^ok	.*/Dep/Used.olean" "$EVENTS" || fail "Dep.Used is not pure: $(grep "/Dep/Used.olean" "$EVENTS")"
capture lake paperlean status
check_out_contains "Dep.Top7 runs in the interpreter where no plugin loads it: it imports Dep.Base, which is not built"

# Built again, Dep.Base is the same module, and the modules that import it keep their files and run
# in the interpreter; the results are those without native code.
run lake build Dep
[ -f "$OLEAN" ] || fail "Dep.Base was not built again"
capture env PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean Use.lean
check_out_matches "paperlean-timing native libs=1 "
{ grep -v "^paperlean-" "$CAPTURED.out.produced" || true; } | $DIFF -- "$TMP_DIR/plain.out" - ||
  fail "the native library changes the output"
