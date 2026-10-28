# Tests the `paperlean` command (`lake paperlean`, `src/lake/Lake/PaperLean/`) and Lake's use of
# prepared data (`.lake/paperlean/`): checks before changing anything, the data reaching `lean`
# through the environment for the Lake that `paperlean` commands run (`PAPERLEAN_ACCELERATE`) and
# not for plain `lake`, without entering traces, explicit variables winning, damaged or foreign data
# being ignored, and the front end that `paperlean install` writes, which finds the PaperLean
# toolchain for the Lean version of a project that keeps Lean's own toolchain.

unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN
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
ls .lake/paperlean/deps-*/deps.paperlean .lake/paperlean/deps-*/deps.image.paperlean \
  .lake/paperlean/native-*/dep.paperlean > /dev/null || fail "prepare did not write its files"
[ -e .lake/paperlean/deps-*/tmp ] && fail "prepare left its temporary directory"
capture lake paperlean status
check_out_contains "prepared data"
check_out_contains "used: 1 pack(s), an import image, 1 native libraries"
check_out_contains "native library of dep: 2 modules"

# Plain `lake` does not use the data; the Lake of `paperlean` commands passes it to the `lean`
# processes it starts, which use it.
capture_exit 1 lake env printenv LEAN_OLEAN_PACK
capture env PAPERLEAN_IMPORT_TIMING=1 lake lean Root/Main.lean
! grep -q "modules.fast packed=[1-9]" "$CAPTURED.out.produced" || fail "plain lake used prepared data"
capture env PAPERLEAN_ACCELERATE=1 lake env printenv LEAN_OLEAN_PACK
check_out_matches "$WS/.lake/paperlean/deps-[0-9]*/deps.paperlean"
capture env PAPERLEAN_ACCELERATE=1 lake env printenv LEAN_IMPORT_IMAGE
check_out_matches "$WS/.lake/paperlean/deps-[0-9]*/deps.image.paperlean"
capture env PAPERLEAN_IMPORT_TIMING=1 env PAPERLEAN_ACCELERATE=1 lake lean Root/Main.lean
check_out_matches "paperlean-timing modules.fast packed=[1-9]"
check_out_contains "paperlean-timing native libs=1 modules=2"
# A moved project keeps its data: packs record the project's roots, and manifests their library,
# relative to themselves.
cd "$TMP_DIR"; mv ws ws2; cd ws2
capture env PAPERLEAN_IMPORT_TIMING=1 env PAPERLEAN_ACCELERATE=1 lake lean Root/Main.lean
check_out_matches "paperlean-timing modules.fast packed=[1-9]"
check_out_contains "paperlean-timing native libs=1 modules=2"
cd "$TMP_DIR"; mv ws2 ws; cd ws

# A run that writes new data deletes the old; a `.c` file that does not match its module's trace is
# left out of the native library.
OLD=$(ls -d .lake/paperlean/deps-*)
echo "/* changed */" >> ../dep/.lake/build/ir/Dep/A.c
capture lake paperlean prepare
check_out_contains "1 modules, 1 left out"
check_out_contains "Dep.A: .c does not match the trace"
[ -e "$OLD" ] && fail "prepare kept the data it replaced"
# Dep imports Dep.A, whose code would be its native callee: neither is native now
capture env PAPERLEAN_IMPORT_TIMING=1 env PAPERLEAN_ACCELERATE=1 lake lean Root/Main.lean
check_out_contains "paperlean-timing native libs=0 modules=0 meta=0 verified=1 importsNotUsed=1"
perl -i -ne 'print unless eof' ../dep/.lake/build/ir/Dep/A.c
capture lake paperlean prepare
check_out_contains "native library of dep" ; check_out_contains "2 modules"

# The files of a module that no longer exists (Lake keeps them, e.g. after an update renamed the
# module) are left out of packs and native libraries; here they define the same symbols as Dep.A.
PACKED=$(grep -o "[0-9]* files" "$CAPTURED.out.produced" | head -1)
for f in ../dep/.lake/build/lib/lean/Dep/A.* ../dep/.lake/build/ir/Dep/A.*; do cp "$f" "${f/\/A./\/Old.}"; done
capture lake paperlean prepare
check_out_contains "  $PACKED"
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
echo garbage > .lake/paperlean/env.json
capture env PAPERLEAN_ACCELERATE=1 lake env sh -c 'echo "packs=$LEAN_OLEAN_PACK"'
grep -q paperlean "$CAPTURED.out.produced" && fail "damaged data is used"
capture lake paperlean status
check_out_contains "is damaged"
cp "$TMP_DIR/env.json" .lake/paperlean/env.json

# `paperlean build` reports the data once and stops before building dependencies of another Lean;
# with --lean-heartbeats, Lean's heartbeat counting reaches `lean`.
capture lake paperlean build
check_out_contains "PaperLean prepared data: used"
cat > Root/Probe.lean <<'END'
#eval show IO Unit from do IO.println s!"heartbeats={(← IO.getEnv "PAPERLEAN_HEARTBEATS").getD "-"}"
END
capture lake paperlean build --lean-heartbeats Root.Probe
check_out_contains "heartbeats=lean"
rm Root/Probe.lean
touch ../dep/.lake/build/lib/lean/Dep/A.olean
capture lake paperlean status
check_out_matches "deps.paperlean: .*, 1 of [0-9]+ modules changed since packing"
capture lake paperlean build
check_out_matches "1 of [0-9]+ packed modules changed since packing"
echo "leanprover/lean4:v4.0.0" > ../dep/lean-toolchain
capture_exit 1 lake paperlean build
check_out_contains "dep asks for Lean 4.0.0 (its lean-toolchain)"
check_out_contains "Nothing was built"
capture lake paperlean build --rebuild-deps
rm ../dep/lean-toolchain
capture lake paperlean prepare --no-native

# A platform without native libraries (Windows for now): prepare says so and does everything else.
capture env PAPERLEAN_NO_NATIVE_PLATFORM=1 lake paperlean prepare
check_out_contains "Native libraries are not available for"
check_out_contains "Prepared"
! grep -Fq "Compiling the native library" "$CAPTURED.out.produced" || fail "prepare compiled native code"
capture lake paperlean status
check_out_contains "used: 1 pack(s), an import image"
! grep -Fq "native libraries" "$CAPTURED.out.produced" || fail "native libraries in use"

# Not enough disk space: nothing changes.
cp .lake/paperlean/env.json "$TMP_DIR/env.before"
capture_exit 1 env PAPERLEAN_FREE_SPACE=1000 lake paperlean prepare
check_out_contains "of disk space in"
check_out_contains "Nothing was changed"
cmp .lake/paperlean/env.json "$TMP_DIR/env.before" || fail "prepare changed the data without disk space"
# While another process holds the lock (the operating system's lock on `.lake/paperlean.lock`, as
# `paperlean` commands take it), prepare and clean refuse at once and change nothing.
cat > "$TMP_DIR/Hold.lean" <<'EOF'
-- (until the file `release` exists, or `held` no longer does: the test ended)
def main (args : List String) : IO Unit := do
  let h ← IO.FS.Handle.mk args[0]! .append
  h.lock
  IO.FS.writeFile args[1]! ""
  while !(← System.FilePath.pathExists args[2]!) && (← System.FilePath.pathExists args[1]!) do
    IO.sleep 20
  h.unlock
EOF
lean --run "$TMP_DIR/Hold.lean" .lake/paperlean.lock "$TMP_DIR/held" "$TMP_DIR/release" > /dev/null 2>&1 &
HOLDER=$!
while [ ! -e "$TMP_DIR/held" ]; do sleep 0.05; done
capture_exit 1 lake paperlean prepare --no-native
check_out_contains "another paperlean command is changing the prepared data"
capture_exit 1 lake paperlean clean
check_out_contains "another paperlean command is changing the prepared data"
touch "$TMP_DIR/release"; wait $HOLDER
cmp .lake/paperlean/env.json "$TMP_DIR/env.before" || fail "a command changed the data while locked"
# The lock ends with its process, so the lock file left behind does not block, and no command
# deletes it (a process that opened a deleted lock file would lock a file the others no longer see).
# An interrupted run leaves a directory that env.json does not refer to; the next run deletes it.
mkdir -p .lake/paperlean/deps-1/native
capture lake paperlean prepare --no-native
[ -e .lake/paperlean/deps-1 ] && fail "prepare kept the directory of an interrupted run"
[ -e .lake/paperlean.lock ] || fail "prepare deleted the lock file"
# Commands started together: each completes or refuses as above, and the data they leave is whole.
for i in 1 2 3 4 5 6; do
  if [ $i = 3 ]; then cmd=clean; else cmd="prepare --no-native"; fi
  (set +e; lake paperlean $cmd > "$TMP_DIR/together-$i.out" 2>&1; echo $? > "$TMP_DIR/together-$i.exit") &
done
wait
for i in 1 2 3 4 5 6; do
  if [ "$(cat "$TMP_DIR/together-$i.exit")" != 0 ]; then
    grep -Fq "another paperlean command is changing the prepared data" "$TMP_DIR/together-$i.out" ||
      { cat "$TMP_DIR/together-$i.out"; fail "a command started together with others failed"; }
  fi
done
[ -e .lake/paperlean.lock ] || fail "clean deleted the lock file"
capture lake paperlean prepare --no-native
check_out_contains "Prepared"
capture lake paperlean status
check_out_contains "used: 1 pack(s), an import image"

# --all packs the root package too; clean deletes everything.
capture lake paperlean prepare --all --no-native
check_out_contains "of root"
capture env PAPERLEAN_ACCELERATE=1 lake env printenv LEAN_OLEAN_PACK
check_out_matches "$WS/.lake/paperlean/deps-[0-9]*/deps.paperlean:$WS/.lake/paperlean/root-[0-9]*/root.paperlean"
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
cd "$TMP_DIR"
capture_exit 1 env ELAN_HOME="$TMP_DIR/elan" sh "$FE" status
check_out_contains "not inside a Lake workspace"
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
printf '#!/bin/sh\necho old PaperLean\n' > "$TMP_DIR/elan/toolchains/me--PaperLean---v0.0.9-lean$LEANVER/bin/paperlean"
chmod +x "$TMP_DIR/elan/toolchains/me--PaperLean---v0.0.9-lean$LEANVER/bin/paperlean"
capture env ELAN_HOME="$TMP_DIR/elan" sh "$FE" --version
check_out_contains "PaperLean "
! grep -q "old PaperLean" "$CAPTURED.out.produced" || fail "the front end did not take the newest release"
capture env ELAN_HOME="$TMP_DIR/elan" PAPERLEAN_TOOLCHAIN="$TMP_DIR/elan/toolchains/me--PaperLean---v0.0.9-lean$LEANVER" sh "$FE" --version
check_out_contains "old PaperLean"
mkdir -p "$TMP_DIR/official/bin"
capture_exit 1 env ELAN_HOME="$TMP_DIR/elan" PAPERLEAN_TOOLCHAIN="$TMP_DIR/official" sh "$FE" --version
check_out_contains "is not an installed PaperLean toolchain"
echo "$TC" > lean-toolchain
capture env ELAN_HOME="$TMP_DIR/elan" sh "$FE" --version
check_out_contains "PaperLean "
