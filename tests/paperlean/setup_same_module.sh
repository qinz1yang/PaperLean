# Execute as a standard tests/paperlean shell fixture. The two compilers never write
# their artifacts simultaneously; the first pauses before Lean has opened its setup.
cd "$TMP_DIR"
export REAL_LEAN="$(command -v lean)"
real_root="$("$REAL_LEAN" --print-prefix)"
export REAL_LEANIR="$real_root/bin/leanir"
fake="$PWD/sysroot"
mkdir -p "$fake/bin" ws
for d in "$real_root"/*; do
  if [ "${d##*/}" != bin ]; then ln -s "$d" "$fake/${d##*/}"; fi
done
for f in "$real_root/bin"/*; do
  case "${f##*/}" in lean|leanir) ;; *) ln -s "$f" "$fake/bin/${f##*/}";; esac
done
cat > "$fake/bin/lean" <<'SH'
#!/bin/sh
setup=
for arg do
  if [ "${prev:-}" = --setup ]; then setup=$arg; break; fi
  prev=$arg
done
for arg do
  case "$arg" in
    *Use.lean)
      if [ -n "${GATE_BEFORE_SETUP:-}" ]; then
        printf '%s\n' "$setup" > "$GATE_BEFORE_SETUP.path"
        cp "$setup" "$GATE_BEFORE_SETUP.initial" || exit 95
        : > "$GATE_BEFORE_SETUP.ready"
        for n in $(seq 300); do [ -e "$GATE_BEFORE_SETUP.go" ] && break; sleep .1; done
        [ -e "$GATE_BEFORE_SETUP.go" ] || exit 96
      fi ;;
  esac
done
exec "$REAL_LEAN" "$@"
SH
cat > "$fake/bin/leanir" <<'SH'
#!/bin/sh
case "$2" in
  *Use.ir)
    if [ -n "${GATE_BEFORE_SETUP:-}" ]; then
      [ "$1" = "$(cat "$GATE_BEFORE_SETUP.path")" ] || exit 97
      cmp -s "$1" "$GATE_BEFORE_SETUP.initial" || exit 98
      : > "$GATE_BEFORE_SETUP.leanir"
    fi ;;
esac
exec "$REAL_LEANIR" "$@"
SH
chmod +x "$fake/bin/lean" "$fake/bin/leanir"
export LAKE_OVERRIDE_LEAN=1 LEAN_SYSROOT="$fake" LAKE_ARTIFACT_CACHE=false PAPERLEAN_BUILD_PACKS=0
unset PAPERLEAN_SETUP_INDEX_KEEP
cd ws
cat > lakefile.lean <<'LEAN'
import Lake
open Lake DSL
package probe
lean_lib Leaf
@[default_target] lean_lib Use where
  leanOptions := #[⟨`compiler.postponeCompile, true⟩]
script buildUse (args) do
  let ws ← getWorkspace
  let alias := Lake.DSL.mkModuleFacetDecl ModuleExportInfo `exportInfo fun mod =>
    Lake.Module.exportInfoFacetConfig.run mod
  let ws := if args == ["fallback"] then ws.addModuleFacetConfig alias.config else ws
  let some m := ws.findModule? `Use | error "missing Use"
  discard <| ws.runBuild m.leanArts.fetch
  return 0
LEAN
printf 'module\n@[expose] public def leaf := 7\n' > Leaf.lean
printf 'module\npublic import Leaf\n@[expose] public def readLeaf := leaf\nexample : readLeaf = 7 := rfl\n' > Use.lean
mkdir -p "$TMP_DIR/unrelated-tree" .lake/paperlean-setup
printf 'keep\n' > "$TMP_DIR/unrelated-tree/marker"
ln -s "$TMP_DIR/unrelated-tree" .lake/paperlean-setup/99999999-42
run lake build Leaf
gate="$TMP_DIR/gate"
for mode in plain indexed fallback; do
  if [ "$mode" = plain ]; then acc=0; else acc=1; fi
  gate="$TMP_DIR/gate-$mode"
  if [ -d .lake/build ]; then
    # Clear only Use, preserving the prebuilt dependency and keeping both compilers' source identical.
    find .lake/build -name 'Use.*' -type f -delete
  fi
  env PAPERLEAN_ACCELERATE="$acc" GATE_BEFORE_SETUP="$gate" lake run buildUse "$mode" >"$TMP_DIR/first-$mode.log" 2>&1 &
  first=$!
  for n in $(seq 300); do [ -e "$gate.ready" ] && break; sleep .1; done
  [ -e "$gate.ready" ] || { cat "$TMP_DIR/first-$mode.log"; fail "wrapper did not intercept Use"; }
  if [ "$mode" = indexed ]; then
    grep -q 'paperlean-setup' "$gate.initial" || fail "first invocation did not index"
  else
    ! grep -q 'paperlean-setup' "$gate.initial" || fail "$mode did not use a complete setup"
  fi
  run env PAPERLEAN_ACCELERATE="$acc" lake run buildUse indexed
  : > "$gate.go"
  wait "$first" || { cat "$TMP_DIR/first-$mode.log"; fail "first run read a retired second setup"; }
  [ -e "$gate.leanir" ] || fail "postponed leanir subprocess did not read the launch setup"
done
[ -z "$(find .lake/paperlean-setup -name 'launch-*.paperlean' -print 2>/dev/null)" ] ||
  fail "a compiler launch file remained after its children finished"
[ -z "$(find .lake/paperlean-setup -mindepth 1 -maxdepth 1 -type d -print 2>/dev/null)" ] ||
  fail "a launch-only generation directory survived cleanup"
[ -f "$TMP_DIR/unrelated-tree/marker" ] || fail "interrupted cleanup followed a generation symlink"
