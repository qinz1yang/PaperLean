# CTest runs each tests/pkg subdirectory's run_test.sh in the stage environment.
case "$OSTYPE" in
    msys*|cygwin*) ;;
    *) exit 0 ;;
esac
set -euo pipefail
work="$TMP_DIR/windows spawn"
mkdir -p "$work"
# The independent CRT child needs no Lean DLLs, even with an empty environment.
"${CC:-cc}" -std=c11 -O2 -static -municode probe.c -o "$work/probe.exe"
"${CC:-cc}" -std=c11 -O2 -static -municode -mwindows absent.c -o "$work/absent.exe"
lean --c="$work/Main.c" -Dcompiler.postponeCompile=false Main.lean
leanc ${LEANC_OPTS-} -O2 -c event.c -o "$work/event.o"
leanc ${LEANC_OPTS-} -O2 -o "$work/parent.exe" "$work/Main.c" "$work/event.o" -leanshared -lleanshared
export V023_KEEP=parent V023_REMOVE=remove V023_MIXED=parent
probe=$(cygpath -aw "$work/probe.exe")
for mode in argv environment handles stdio absent cwd; do
    timeout 45s "$work/parent.exe" "$probe" "$mode"
done
