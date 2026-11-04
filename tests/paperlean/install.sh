# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests the `paperlean` command (`lake paperlean`, `src/lake/Lake/PaperLean/`) and Lake's use of
# prepared data (`.lake/paperlean/`): checks before changing anything, the data reaching `lean`
# through the environment for the Lake that `paperlean` commands run (`PAPERLEAN_ACCELERATE`) and
# not for plain `lake`, without entering traces, explicit variables winning, damaged or foreign data
# being ignored, and the front end that `paperlean install` writes, which finds the PaperLean
# toolchain for the Lean version of a project that keeps Lean's own toolchain.

WS="$(cd "$TMP_DIR" && pwd -P)/ws"
mkdir -p "$TMP_DIR/dep/Dep" "$WS/Root"
cat > "$TMP_DIR/dep/lakefile.toml" <<'END'
name = "dep"
defaultTargets = ["Dep"]
[[lean_lib]]
name = "Dep"
END
cat > "$TMP_DIR/dep/Dep.lean" <<'END'
import Dep.A
END
cat > "$TMP_DIR/dep/Dep/A.lean" <<'END'
def depValue : Nat := 41
@[simp] theorem depValue_eq : depValue = 41 := rfl
END
cat > "$WS/lakefile.toml" <<'END'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "dep"
path = "../dep"
[[lean_lib]]
name = "Root"
END
cat > "$WS/Root.lean" <<'END'
import Root.Main
END
cat > "$WS/Root/Main.lean" <<'END'
import Dep
def rootValue : Nat := depValue + 1
example : depValue = 41 := by simp
END
cd "$WS"

capture lake paperlean --version
check_out_contains "PaperLean "
check_out_contains "Lean $(lean --version | sed -n 's/^Lean (version \([^,]*\),.*/\1/p'), commit "

# Nothing is prepared before the dependencies are built.
capture_exit 1 lake paperlean prepare
check_out_contains "2 modules of the dependencies that root imports are not built"
check_out_contains "Nothing was changed"
[ -e .lake/paperlean/env.json ] && fail "prepare wrote data although the dependencies are not built"

run lake build
# a misspelt name changes nothing
capture_exit 1 lake paperlean prepare dpe
check_out_contains "did you mean the package dep?"

capture lake paperlean prepare -j 2
check_out_contains "Prepared"
check_out_contains "Compiling the native library of dep"
[ -f .lake/paperlean/env.json ] || fail "prepare did not write env.json"
ls .lake/paperlean/bind/dep-*.paperlean .lake/paperlean/image-*/image.paperlean \
  "$PAPERLEAN_CACHE_DIR"/prepared/*/native/dep-*/dep.paperlean > /dev/null || fail "prepare did not write its files"
[ -e .lake/paperlean/image-*/tmp ] && fail "prepare left its temporary directory"
capture lake paperlean status
check_out_contains "prepared data"
check_out_contains "used: 2 pack(s), an import image, 1 native libraries"
check_out_contains "native library of dep: 2 modules"

# Plain `lake` does not use the data; the Lake of `paperlean` commands passes it to the `lean`
# processes it starts, which use it.
capture_exit 1 lake env printenv LEAN_OLEAN_PACK
capture env PAPERLEAN_IMPORT_TIMING=1 lake lean Root/Main.lean
! grep -q "modules.fast packed=[1-9]" "$CAPTURED.out.produced" || fail "plain lake used prepared data"
capture env PAPERLEAN_ACCELERATE=1 lake env printenv LEAN_OLEAN_PACK
check_out_matches "$WS/.lake/paperlean/bind/dep-[0-9a-f]+\.paperlean"
capture env PAPERLEAN_ACCELERATE=1 lake env printenv LEAN_IMPORT_IMAGE
check_out_matches "$WS/.lake/paperlean/image-[0-9]*/image.paperlean"
capture env PAPERLEAN_IMPORT_TIMING=1 env PAPERLEAN_ACCELERATE=1 lake lean Root/Main.lean
check_out_matches "paperlean-timing modules.fast packed=[1-9]"
check_out_contains "paperlean-timing native libs=1 modules=2"
# A moved project keeps its data: bindings record the project's roots relative to themselves (the
# packs and libraries are in the cache).
cd "$TMP_DIR"; mv ws ws2; cd ws2
capture env PAPERLEAN_IMPORT_TIMING=1 env PAPERLEAN_ACCELERATE=1 lake lean Root/Main.lean
check_out_matches "paperlean-timing modules.fast packed=[1-9]"
check_out_contains "paperlean-timing native libs=1 modules=2"
cd "$TMP_DIR"; mv ws2 ws; cd ws

# The entry of the cache that the data uses, `pack` or `native`.
entry() { grep -o "\"prepared/[^\"]*/$1/dep-[0-9a-f]*" .lake/paperlean/env.json | head -1; }
# A run that writes new data replaces the old; a `.c` file that does not match its module's trace is
# left out of the native library.
OLD=$(entry native)
echo "/* changed */" >> ../dep/.lake/build/ir/Dep/A.c
capture lake paperlean prepare
check_out_contains "1 modules, 1 left out"
check_out_contains "Dep.A: .c does not match the trace"
[ "$(entry native)" != "$OLD" ] || fail "prepare kept the library it replaced"
# Dep imports Dep.A, whose code would be its native callee: neither is native now
capture env PAPERLEAN_IMPORT_TIMING=1 env PAPERLEAN_ACCELERATE=1 lake lean Root/Main.lean
check_out_contains "paperlean-timing native libs=0 modules=0 meta=0 verified=1 importsNotUsed=1"
perl -i -ne 'print unless eof' ../dep/.lake/build/ir/Dep/A.c
capture lake paperlean prepare
check_out_contains "dep: 2 modules (from the cache)"
[ "$(entry native)" = "$OLD" ] || fail "prepare did not take the library from the cache again"

# The files of a module that no longer exists (Lake keeps them, e.g. after an update renamed the
# module) are left out of packs and native libraries; here they define the same symbols as Dep.A.
PACKED=$(entry pack)
for f in ../dep/.lake/build/lib/lean/Dep/A.* ../dep/.lake/build/ir/Dep/A.*; do cp "$f" "${f/\/A./\/Old.}"; done
capture lake paperlean prepare
[ "$(entry pack)" = "$PACKED" ] || fail "the files of a module that no longer exists were packed"
check_out_contains "2 modules"
! grep -Fq "could not be built" "$CAPTURED.out.produced" || fail "a module that no longer exists broke the native library"
rm ../dep/.lake/build/lib/lean/Dep/Old.* ../dep/.lake/build/ir/Dep/Old.*
# A native library that cannot be built is reported, in prepare's output and in status.
cp ../dep/lakefile.toml "$TMP_DIR/dep-lakefile.toml"
echo 'moreLinkArgs = ["-lpaperlean-no-such-library"]' >> ../dep/lakefile.toml
capture lake paperlean prepare
check_out_contains "the native library of dep could not be built"
check_out_contains "warning: no native library for dep"
capture lake paperlean status
check_out_contains "native library of dep: not built ("
cp "$TMP_DIR/dep-lakefile.toml" ../dep/lakefile.toml
capture lake paperlean prepare
check_out_contains "2 modules"

# The data enters neither traces nor outputs: rebuilding with and without it gives the same files.
echo "-- rebuilt" >> Root/Main.lean
run env PAPERLEAN_ACCELERATE=1 lake build
cp .lake/build/lib/lean/Root/Main.trace "$TMP_DIR/with.trace"
cp .lake/build/lib/lean/Root/Main.olean "$TMP_DIR/with.olean"
mv .lake/paperlean "$TMP_DIR/saved-data"
echo "-- rebuilt again" >> Root/Main.lean
run lake build
perl -i -ne 'print unless eof' Root/Main.lean
run lake build
$DIFF -- "$TMP_DIR/with.trace" .lake/build/lib/lean/Root/Main.trace || fail "the trace differs with prepared data"
cmp "$TMP_DIR/with.olean" .lake/build/lib/lean/Root/Main.olean || fail "the .olean differs with prepared data"
mv "$TMP_DIR/saved-data" .lake/paperlean

# Explicit variables win over prepared data, which is then not used at all.
capture env LEAN_OLEAN_PACK=/nonexistent env PAPERLEAN_ACCELERATE=1 lake env sh -c 'echo "image=$LEAN_IMPORT_IMAGE"'
check_out_contains "image="
grep -q paperlean "$CAPTURED.out.produced" && fail "prepared data is mixed with explicit variables"
capture env LEAN_OLEAN_PACK=/nonexistent lake paperlean status
check_out_contains "not used: LEAN_OLEAN_PACK set explicitly"

# Data from another version, or damaged data, is not used, and status says why.
cp .lake/paperlean/env.json "$TMP_DIR/env.json"
perl -pi -e 's/"paperlean": "[^"]*"/"paperlean": "0.0.1-lean4.0.0"/' .lake/paperlean/env.json
capture env PAPERLEAN_ACCELERATE=1 lake env sh -c 'echo "packs=$LEAN_OLEAN_PACK"'
grep -q paperlean "$CAPTURED.out.produced" && fail "data of another version is used"
capture lake paperlean status
check_out_contains "not used: it was prepared by PaperLean 0.0.1-lean4.0.0"
cp "$TMP_DIR/env.json" .lake/paperlean/env.json
perl -pi -e 's/"build": "[^"]*"/"build": "000000000000"/' .lake/paperlean/env.json
grep -q '"build": "000000000000"' .lake/paperlean/env.json || fail "env.json does not record the build"
capture env PAPERLEAN_ACCELERATE=1 lake env sh -c 'echo "packs=$LEAN_OLEAN_PACK"'
grep -q paperlean "$CAPTURED.out.produced" && fail "data of another build is used"
capture lake paperlean status
check_out_contains "not used: it was prepared by another build of PaperLean"
echo garbage > .lake/paperlean/env.json
capture env PAPERLEAN_ACCELERATE=1 lake env sh -c 'echo "packs=$LEAN_OLEAN_PACK"'
grep -q paperlean "$CAPTURED.out.produced" && fail "damaged data is used"
capture lake paperlean status
check_out_contains "is damaged"
cp "$TMP_DIR/env.json" .lake/paperlean/env.json

# `paperlean build` reports the data once and stops before building dependencies of another Lean.
capture lake paperlean build
check_out_contains "PaperLean prepared data: used"
# What `lean` warns about the prepared data goes to a file, not into Lake's traces, from which later
# builds, also official ones, would repeat it.
PACK=$(ls .lake/paperlean/bind/dep-*.paperlean | head -1)
mv "$PACK" "$PACK.saved"
echo garbage > "$PACK"
echo "-- warned" >> Root/Main.lean
capture lake paperlean build
check_out_contains "warning(s) about the prepared data"
WARNINGS=$(sed -n 's/.*about the prepared data, in \(.*\); .*/\1/p' "$CAPTURED.out.produced")
case $WARNINGS in */.lake/paperlean-warnings-[0-9]*.paperlean) ;; *) fail "no warnings file of the run: '$WARNINGS'" ;; esac
# PaperLean's files in `.lake` are its data directory and side files
side_files_only() {
  for f in .lake/paperlean*; do
    case $f in
      .lake/paperlean|*.paperlean) ;;
      .lake/paperlean-setup)
        [ -d "$f" ] && [ -z "$(ls -A "$f")" ] || fail "the build left setup indexes: $f"
        ;;
      *) fail "PaperLean data outside .lake/paperlean and side files: $f" ;;
    esac
  done
}
side_files_only
grep -q "ignoring olean pack" "$WARNINGS" || fail "the warning is not in the file"
! grep -q "ignoring olean pack" "$CAPTURED.out.produced" || fail "the warning reached Lake's output"
capture lake build
! grep -q "ignoring olean pack" "$CAPTURED.out.produced" || fail "Lake repeated the warning"
# A pack that every `lean` ignores is not reported as used, also when nothing is compiled, and a user
# can read why: here a binding that is no binding, and a pack of the cache that has another identity,
# as after a copy, which `prepare` writes again.
capture lake paperlean status
check_out_contains "used in part: 1 of 2 pack(s), but not "
check_out_contains "not a PaperLean side file; run \`paperlean prepare\`"
capture lake paperlean build
check_out_contains "PaperLean prepared data: used in part: "
mv -f "$PACK.saved" "$PACK"
CACHED=$(ls "$PAPERLEAN_CACHE_DIR"/prepared/*/pack/dep-*/pack.paperlean)
cp -p "$CACHED" "$TMP_DIR/pack.copy"
mv -f "$TMP_DIR/pack.copy" "$CACHED"
capture lake paperlean status
check_out_contains "it changed since it was written; run \`paperlean prepare\`"
! grep -q "packStaleness" "$CAPTURED.out.produced" || fail "status shows an internal name"
capture lake paperlean build
check_out_contains "PaperLean prepared data: used in part: "
perl -i -ne 'print unless eof' Root/Main.lean
capture lake paperlean prepare -j 2
check_out_contains "Prepared"
check_out_contains "Packing dep"
capture lake paperlean status
check_out_contains "used: 2 pack(s), an import image, 1 native libraries"
# a run without warnings keeps no file, and the files of runs that ended are removed
capture lake paperlean build
! grep -q "warning(s) about the prepared data" "$CAPTURED.out.produced" || fail "warnings without a damaged pack"
ls .lake/paperlean-warnings-* 2> /dev/null && fail "warnings files are left"
touch ../dep/.lake/build/lib/lean/Dep/A.olean
capture lake paperlean status
check_out_matches "package dep: prepared: pack dep-[0-9a-f]+ of the cache \([0-9]+ modules, 1 changed since and read from disk\)"
capture lake paperlean build
check_out_matches "1 of [0-9]+ packed modules changed since packing"
# A dependency that asks for another Lean release: a note if this Lean built it (which decides whether
# it is rebuilt); if it is not built, the build stops unless asked to build it.
echo "leanprover/lean4:v4.0.0" > ../dep/lean-toolchain
capture lake paperlean build
check_out_contains "Note: dep asks for Lean 4.0.0 (its lean-toolchain), but this Lean built it."
mv ../dep/.lake/build "$TMP_DIR/dep-build"
capture_exit 1 lake paperlean build
check_out_contains "dep asks for Lean 4.0.0 (its lean-toolchain)"
check_out_contains "Nothing was built"
capture_exit 3 lake paperlean build --rebuild-deps --no-build
mv "$TMP_DIR/dep-build" ../dep/.lake/build
rm ../dep/lean-toolchain
capture lake paperlean prepare --no-native

# A platform without native libraries (Windows for now): prepare says so and does everything else.
capture env PAPERLEAN_NO_NATIVE_PLATFORM=1 lake paperlean prepare
check_out_contains "Native libraries are not available for"
check_out_contains "Prepared"
! grep -Fq "Compiling the native library" "$CAPTURED.out.produced" || fail "prepare compiled native code"
capture lake paperlean status
check_out_contains "used: 2 pack(s), an import image"
! grep -Fq "native libraries" "$CAPTURED.out.produced" || fail "native libraries in use"

# Not enough disk space for what is not in the cache: nothing changes. (What is in the cache needs none.)
cp .lake/paperlean/env.json "$TMP_DIR/env.before"
run env PAPERLEAN_FREE_SPACE=1000 lake paperlean prepare --no-native
cmp .lake/paperlean/env.json "$TMP_DIR/env.before" || fail "prepare with everything in the cache changed the data"
mv "$PAPERLEAN_CACHE_DIR/prepared" "$TMP_DIR/prepared.saved"
capture_exit 1 env PAPERLEAN_FREE_SPACE=1000 lake paperlean prepare
check_out_contains "of disk space in"
check_out_contains "Nothing was changed"
cmp .lake/paperlean/env.json "$TMP_DIR/env.before" || fail "prepare changed the data without disk space"
rm -rf "$PAPERLEAN_CACHE_DIR/prepared"
mv "$TMP_DIR/prepared.saved" "$PAPERLEAN_CACHE_DIR/prepared"
# While another process holds the lock (the operating system's lock on
# `.lake/paperlean-lock.paperlean`, as `paperlean` commands take it), prepare and clean refuse at once
# and change nothing.
cat > "$TMP_DIR/Hold.lean" <<'EOF'
-- (until the file `release` exists, or `held` no longer does: the test ended; at most five minutes;
-- with a fourth argument, shared, as `paperlean build` holds it)
def main (args : List String) : IO Unit := do
  let h ← IO.FS.Handle.mk args[0]! .append
  h.lock (exclusive := args.length < 4)
  IO.FS.writeFile args[1]! ""
  let deadline := (← IO.monoMsNow) + 300000
  while !(← System.FilePath.pathExists args[2]!) && (← System.FilePath.pathExists args[1]!) &&
      (← IO.monoMsNow) < deadline do
    IO.sleep 20
  h.unlock
EOF
# starts a process that holds the lock (shared with an argument) and waits until it does
hold_lock() {
  lean --run "$TMP_DIR/Hold.lean" .lake/paperlean-lock.paperlean "$TMP_DIR/held" "$TMP_DIR/release" "$@" > "$TMP_DIR/hold.out" 2>&1 &
  HOLDER=$!
  local waited=0
  while [ ! -e "$TMP_DIR/held" ]; do
    kill -0 $HOLDER 2> /dev/null || { cat "$TMP_DIR/hold.out"; fail "the process that takes the lock ended"; }
    [ $waited -lt 2400 ] || fail "the lock was not taken within two minutes"
    sleep 0.05; waited=$((waited + 1))
  done
}
hold_lock
capture_exit 1 lake paperlean prepare --no-native
check_out_contains "another paperlean command is changing the prepared data"
capture_exit 1 lake paperlean clean
check_out_contains "another paperlean command is changing the prepared data"
capture_exit 1 lake paperlean build
check_out_contains "Nothing was built"
# (downloads use the data as builds do)
capture_exit 1 lake paperlean cache get some-argument
check_out_contains "Nothing was downloaded"
touch "$TMP_DIR/release"; wait $HOLDER
rm "$TMP_DIR/held" "$TMP_DIR/release"
# While a build uses the data (a shared lock), prepare and clean refuse too, saying why.
hold_lock shared
capture_exit 1 lake paperlean prepare --no-native
check_out_contains "a paperlean build is using the prepared data"
capture_exit 1 lake paperlean clean
check_out_contains "a paperlean build is using the prepared data"
touch "$TMP_DIR/release"; wait $HOLDER
cmp .lake/paperlean/env.json "$TMP_DIR/env.before" || fail "a command changed the data while locked"
# The lock ends with its process, so the lock file left behind does not block, and no command
# deletes it (a process that opened a deleted lock file would lock a file the others no longer see).
# An interrupted run leaves a directory that env.json does not refer to; the next run deletes it.
mkdir -p .lake/paperlean/deps-1/native
capture lake paperlean prepare --no-native
[ -e .lake/paperlean/deps-1 ] && fail "prepare kept the directory of an interrupted run"
[ -e .lake/paperlean-lock.paperlean ] || fail "prepare deleted the lock file"
side_files_only
# Commands started together: each completes or refuses as above, within five minutes, and the data
# they leave is whole: every file that env.json refers to exists, the packs read as written, and no
# other directory is left; or, when a clean ended last, nothing is.
TOGETHER=()
for i in 1 2 3 4 5 6; do
  if [ $i = 3 ]; then cmd=clean; else cmd="prepare --no-native"; fi
  (set +e; lake paperlean $cmd > "$TMP_DIR/together-$i.out" 2>&1; echo $? > "$TMP_DIR/together-$i.exit.tmp"
    mv "$TMP_DIR/together-$i.exit.tmp" "$TMP_DIR/together-$i.exit") &
  TOGETHER+=($!)
done
waited=0
while [ "$(ls "$TMP_DIR"/together-*.exit 2> /dev/null | wc -l)" -lt 6 ]; do
  if [ $waited -ge 3000 ]; then
    for p in "${TOGETHER[@]}"; do pkill -P $p || true; kill $p || true; done 2> /dev/null
    fail "commands started together did not end within five minutes"
  fi
  sleep 0.1; waited=$((waited + 1))
done
wait
for i in 1 2 3 4 5 6; do
  if [ "$(cat "$TMP_DIR/together-$i.exit")" != 0 ]; then
    grep -Eq "another paperlean command (is changing|changed) the prepared data" "$TMP_DIR/together-$i.out" ||
      { cat "$TMP_DIR/together-$i.out"; fail "a command started together with others failed"; }
  fi
done
[ -e .lake/paperlean-lock.paperlean ] || fail "clean deleted the lock file"
if [ -e .lake/paperlean/env.json ]; then
  REFS=$(grep -oE '"[a-z]+-[0-9]+/[^"]+"' .lake/paperlean/env.json | tr -d '"')
  [ -n "$REFS" ] || fail "env.json refers to no files after commands started together"
  for f in $REFS; do
    [ -f ".lake/paperlean/$f" ] || fail "after commands started together, env.json refers to the missing $f"
  done
  for d in $(find .lake/paperlean -mindepth 1 -maxdepth 1 -type d); do
    grep -qF "\"${d##*/}/" .lake/paperlean/env.json ||
      fail "after commands started together, ${d##*/} is left, which env.json does not refer to"
  done
  capture lake paperlean status --verify
  check_out_contains "used: 2 pack(s), an import image"
  check_out_contains ", verified"
  ! grep -Eq ": missing|not usable" "$CAPTURED.out.produced" || fail "commands started together left damaged data"
else
  [ -z "$(ls -A .lake/paperlean 2> /dev/null)" ] || fail "commands started together left data without env.json"
fi
capture lake paperlean prepare --no-native
check_out_contains "Prepared"
capture lake paperlean status
check_out_contains "used: 2 pack(s), an import image"

# --all packs the root package too; clean deletes everything.
capture lake paperlean prepare --all --no-native
check_out_contains "of root"
capture env PAPERLEAN_ACCELERATE=1 lake env printenv LEAN_OLEAN_PACK
check_out_matches "$WS/.lake/paperlean/root-[0-9]*/root.paperlean:$WS/.lake/paperlean/bind/dep-[0-9a-f]+\.paperlean:"
# the root package's pack is kept when only the dependencies are prepared again
capture lake paperlean prepare --no-native
capture env PAPERLEAN_ACCELERATE=1 lake env printenv LEAN_OLEAN_PACK
check_out_matches "root-[0-9]*/root.paperlean"
capture lake paperlean clean root
check_out_contains "Deleted the pack of root"
capture env PAPERLEAN_ACCELERATE=1 lake env sh -c 'echo "packs=$LEAN_OLEAN_PACK"'
grep -q root.paperlean "$CAPTURED.out.produced" && fail "clean root left the root pack in use"
capture lake paperlean clean
check_out_contains "Deleted the prepared data"
[ -e .lake/paperlean ] && fail "clean left prepared data"

# The front end: outside a workspace; for a project with Lean's own toolchain, the PaperLean
# toolchain for its Lean version (missing, then installed, the newest of two), a toolchain chosen with
# PAPERLEAN_TOOLCHAIN, and a project whose toolchain is PaperLean.
capture lake paperlean --version
LEANVER=$(sed -n 's/.*-lean//p' "$CAPTURED.out.produced")
mkdir -p "$TMP_DIR/elan/bin" "$TMP_DIR/elan/toolchains"
capture env ELAN_HOME="$TMP_DIR/elan" ELAN_TOOLCHAIN=me/PaperLean:v0.1.0-lean$LEANVER lake paperlean install
check_out_contains "Installed the paperlean command"
FE="$TMP_DIR/elan/bin/paperlean"
# run with another toolchain's name (as the front end runs it), it suggests no release
mkdir -p "$TMP_DIR/elan2/bin"
capture env ELAN_HOME="$TMP_DIR/elan2" ELAN_TOOLCHAIN=leanprover/lean4:v$LEANVER lake paperlean install
grep -qx "suggested=''" "$TMP_DIR/elan2/bin/paperlean" || fail "install suggested another toolchain's name"
cd "$TMP_DIR"
capture_exit 1 env ELAN_HOME="$TMP_DIR/elan" sh "$FE" status
check_out_contains "not inside a Lake workspace"
capture_exit 1 env ELAN_HOME="$TMP_DIR/elan" sh "$FE" --version
check_out_contains "the installed PaperLean toolchains:"
check_out_contains "  none"
cd "$WS"
echo "leanprover/lean4:v$LEANVER" > lean-toolchain
capture_exit 1 env ELAN_HOME="$TMP_DIR/elan" sh "$FE" status
check_out_contains "no PaperLean toolchain for Lean $LEANVER"
check_out_contains "elan toolchain install me/PaperLean:v0.1.0-lean$LEANVER"
echo "leanprover/lean4:v9.9.9" > lean-toolchain
capture_exit 1 env ELAN_HOME="$TMP_DIR/elan" sh "$FE" status
check_out_contains "no PaperLean toolchain for Lean 9.9.9"
check_out_contains "elan toolchain install me/PaperLean:v<version>-lean9.9.9"
TC=$(dirname "$(dirname "$(command -v lake)")")
echo "leanprover/lean4:v$LEANVER" > lean-toolchain
ln -s "$TC" "$TMP_DIR/elan/toolchains/me--PaperLean---v0.1.0-lean$LEANVER"
mkdir -p "$TMP_DIR/elan/toolchains/me--PaperLean---v0.0.9-lean$LEANVER/bin"
printf '#!/bin/sh\necho "old PaperLean, ELAN_TOOLCHAIN=$ELAN_TOOLCHAIN"\n' > "$TMP_DIR/elan/toolchains/me--PaperLean---v0.0.9-lean$LEANVER/bin/paperlean"
chmod +x "$TMP_DIR/elan/toolchains/me--PaperLean---v0.0.9-lean$LEANVER/bin/paperlean"
capture env ELAN_HOME="$TMP_DIR/elan" sh "$FE" --version
check_out_contains "PaperLean "
! grep -q "old PaperLean" "$CAPTURED.out.produced" || fail "the front end did not take the newest release"
# (the newest by version, whatever the names of the origins)
mkdir -p "$TMP_DIR/elan/toolchains/zz--fork---v0.0.8-lean$LEANVER/bin"
printf '#!/bin/sh\necho "old fork"\n' > "$TMP_DIR/elan/toolchains/zz--fork---v0.0.8-lean$LEANVER/bin/paperlean"
chmod +x "$TMP_DIR/elan/toolchains/zz--fork---v0.0.8-lean$LEANVER/bin/paperlean"
capture env ELAN_HOME="$TMP_DIR/elan" sh "$FE" --version
check_out_contains "PaperLean "
! grep -q "old fork" "$CAPTURED.out.produced" || fail "the front end took the last release by name, not the newest"
capture env ELAN_HOME="$TMP_DIR/elan" PAPERLEAN_TOOLCHAIN="$TMP_DIR/elan/toolchains/me--PaperLean---v0.0.9-lean$LEANVER" sh "$FE" --version
# Lake sees the project's toolchain, by which its downloads and caches are keyed, named as elan names it
check_out_contains "old PaperLean, ELAN_TOOLCHAIN=leanprover/lean4:v$LEANVER"
for t in "v$LEANVER" "  $LEANVER " "leanprover/lean4:v$LEANVER  " "leanprover/lean4:$LEANVER"; do
  printf '%s\n' "$t" > lean-toolchain
  capture env ELAN_HOME="$TMP_DIR/elan" PAPERLEAN_TOOLCHAIN="$TMP_DIR/elan/toolchains/me--PaperLean---v0.0.9-lean$LEANVER" sh "$FE" --version
  check_out_contains "old PaperLean, ELAN_TOOLCHAIN=leanprover/lean4:v$LEANVER"
done
echo "leanprover/lean4:v$LEANVER" > lean-toolchain
# a toolchain linked under a name of its own keeps it, as with elan
ln -s "$TMP_DIR/elan/toolchains/me--PaperLean---v0.0.9-lean$LEANVER" "$TMP_DIR/elan/toolchains/mytc"
echo "mytc" > lean-toolchain
capture env ELAN_HOME="$TMP_DIR/elan" sh "$FE" --version
check_out_contains "old PaperLean, ELAN_TOOLCHAIN=mytc"
rm "$TMP_DIR/elan/toolchains/mytc"
# a PaperLean release that is not installed: install it
echo "me/PaperLean:v0.2.0-lean$LEANVER" > lean-toolchain
capture_exit 1 env ELAN_HOME="$TMP_DIR/elan" sh "$FE" status
check_out_contains "the project's toolchain me/PaperLean:v0.2.0-lean$LEANVER is not installed"
check_out_contains "elan toolchain install me/PaperLean:v0.2.0-lean$LEANVER"
echo "leanprover/lean4:v$LEANVER" > lean-toolchain
mkdir -p "$TMP_DIR/official/bin"
capture_exit 1 env ELAN_HOME="$TMP_DIR/elan" PAPERLEAN_TOOLCHAIN="$TMP_DIR/official" sh "$FE" --version
check_out_contains "is not an installed PaperLean toolchain"
echo "$TC" > lean-toolchain
capture env ELAN_HOME="$TMP_DIR/elan" sh "$FE" --version
check_out_contains "PaperLean "
# `--version` where no toolchain can be chosen lists the installed ones
echo "leanprover/lean4:v9.9.9" > lean-toolchain
capture env ELAN_HOME="$TMP_DIR/elan" sh "$FE" --version
check_out_contains "no PaperLean toolchain for Lean 9.9.9"
check_out_contains "  me/PaperLean:v0.1.0-lean$LEANVER"
check_out_contains "  me/PaperLean:v0.0.9-lean$LEANVER"
cd "$TMP_DIR"
capture env ELAN_HOME="$TMP_DIR/elan" sh "$FE" --version
check_out_contains "not inside a Lake workspace; the installed PaperLean toolchains:"
cd "$WS"
echo "$TC" > lean-toolchain
