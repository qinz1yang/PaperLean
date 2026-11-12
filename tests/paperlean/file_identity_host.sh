# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# PaperLean's prepared data (packs, bindings, native library manifests, the hash cache, the setup index,
# source inputs) recognizes an unchanged file by its identity: inode, size, modification and change times.
# The device number is not part of it: on a network filesystem (CephFS, NFS) the same file has a different
# `st_dev` on each machine, so data prepared on one host would look changed on every other one and be
# refused (packs and native libraries unused: plain `.olean` reads, interpreted tactics).
# (1) `fileIdentity`'s device field is 0 and its inode and size are the file's.
# (2) On Linux, with a C compiler: a pack written by one process is used by a process that sees every
#     file with another device number (an `LD_PRELOAD` library adds to `st_dev` in the `stat` family),
#     as by a process on another host of a network filesystem.
cd "$TMP_DIR"
printf 'some bytes\n' > file.txt
cat > id.lean <<'END'
import Lean.PaperLean.System
def main (args : List String) : IO Unit := do
  let some b ← Lean.PaperLean.fileIdentity args[0]! | throw (IO.userError "no identity")
  let w (i : Nat) : Nat := (List.range 8).foldl (fun acc j => acc + (b[8*i+j]!).toNat * 256 ^ j) 0
  IO.println s!"dev={w 0} ino={w 1} size={w 2}"
END
capture lean --run id.lean file.txt
check_out_contains "dev=0 "
case "$(uname -s)" in
  Linux) ino=$(stat -c %i file.txt); size=$(stat -c %s file.txt) ;;
  Darwin) ino=$(stat -f %i file.txt); size=$(stat -f %z file.txt) ;;
  *) exit 0 ;;
esac
check_out_contains "ino=$ino size=$size"

[ "$(uname -s)" = Linux ] || exit 0
cat > fakedev.c <<'END'
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <sys/stat.h>
#include <unistd.h>
static void shifted(dev_t * d) {
    static int said = 0;
    if (!said) { said = 1; static const char m[] = "fake-dev: active\n"; ssize_t r = write(2, m, sizeof m - 1); (void)r; }
    *d += 4096;
}
#define NEXT(T, name) static T next; if (!next) next = (T)dlsym(RTLD_NEXT, name); if (!next) { errno = ENOSYS; return -1; }
/* glibc before 2.33 (the toolchain's sysroot): `stat` and friends call these */
typedef int (*xs_t)(int, const char *, struct stat *);
typedef int (*fxs_t)(int, int, struct stat *);
typedef int (*fxsat_t)(int, int, const char *, struct stat *, int);
typedef int (*xs64_t)(int, const char *, struct stat64 *);
typedef int (*fxs64_t)(int, int, struct stat64 *);
typedef int (*fxsat64_t)(int, int, const char *, struct stat64 *, int);
int __xstat(int v, const char * p, struct stat * b) { NEXT(xs_t, "__xstat") int r = next(v, p, b); if (r == 0) shifted(&b->st_dev); return r; }
int __lxstat(int v, const char * p, struct stat * b) { NEXT(xs_t, "__lxstat") int r = next(v, p, b); if (r == 0) shifted(&b->st_dev); return r; }
int __fxstat(int v, int fd, struct stat * b) { NEXT(fxs_t, "__fxstat") int r = next(v, fd, b); if (r == 0) shifted(&b->st_dev); return r; }
int __fxstatat(int v, int d, const char * p, struct stat * b, int f) { NEXT(fxsat_t, "__fxstatat") int r = next(v, d, p, b, f); if (r == 0) shifted(&b->st_dev); return r; }
int __xstat64(int v, const char * p, struct stat64 * b) { NEXT(xs64_t, "__xstat64") int r = next(v, p, b); if (r == 0) shifted(&b->st_dev); return r; }
int __lxstat64(int v, const char * p, struct stat64 * b) { NEXT(xs64_t, "__lxstat64") int r = next(v, p, b); if (r == 0) shifted(&b->st_dev); return r; }
int __fxstat64(int v, int fd, struct stat64 * b) { NEXT(fxs64_t, "__fxstat64") int r = next(v, fd, b); if (r == 0) shifted(&b->st_dev); return r; }
int __fxstatat64(int v, int d, const char * p, struct stat64 * b, int f) { NEXT(fxsat64_t, "__fxstatat64") int r = next(v, d, p, b, f); if (r == 0) shifted(&b->st_dev); return r; }
#if defined(__GLIBC__) && (__GLIBC__ > 2 || (__GLIBC__ == 2 && __GLIBC_MINOR__ >= 33))
/* glibc 2.33 and later: real functions */
typedef int (*s_t)(const char *, struct stat *);
typedef int (*fs_t)(int, struct stat *);
typedef int (*fsat_t)(int, const char *, struct stat *, int);
int stat(const char * p, struct stat * b) { NEXT(s_t, "stat") int r = next(p, b); if (r == 0) shifted(&b->st_dev); return r; }
int lstat(const char * p, struct stat * b) { NEXT(s_t, "lstat") int r = next(p, b); if (r == 0) shifted(&b->st_dev); return r; }
int fstat(int fd, struct stat * b) { NEXT(fs_t, "fstat") int r = next(fd, b); if (r == 0) shifted(&b->st_dev); return r; }
int fstatat(int d, const char * p, struct stat * b, int f) { NEXT(fsat_t, "fstatat") int r = next(d, p, b, f); if (r == 0) shifted(&b->st_dev); return r; }
#endif
END
if ! ${CC:-cc} -shared -fPIC -O1 -o fakedev.so fakedev.c -ldl > cc.log 2>&1; then
  echo "skipping the cross-host pack check: no C compiler for the LD_PRELOAD library ($(head -1 cc.log))"
  exit 0
fi
mkdir -p lib
printf 'def a := 1\n' > A.lean
printf 'def b := 2\n' > B.lean
printf 'import A\nimport B\n#eval s!"sum={a + b}"\n' > UseAB.lean
run lean -o lib/A.olean A.lean
run lean -o lib/B.olean B.lean
cat > pack.lean <<'END'
import Lean.PaperLean.OLeanPack
def main (args : List String) : IO Unit := do
  let n ← Lean.PaperLean.OLeanPack.create #[args[1]!] args[0]! (baseAddr := 0x200000000000)
  IO.println s!"packed: {n}"
END
capture lean --run pack.lean "$TMP_DIR/ab.paperlean" "$TMP_DIR/lib"
check_out_contains "packed: 2"
# `use <label> <env>...`: imports `UseAB` with the pack, prints the relevant lines, and checks that the pack
# served both modules
use() {
  local label=$1; shift
  env "$@" LEAN_PATH="$TMP_DIR/lib" LEAN_OLEAN_PACK="$TMP_DIR/ab.paperlean" PAPERLEAN_IMPORT_TIMING=1 \
    lean UseAB.lean > "$label.out" 2>&1 || { cat "$label.out"; fail "$label: lean failed"; }
  grep -v '^paperlean-timing ext \|^paperlean-epoch' "$label.out" | sed "s/^/$label: /"
  grep -q '"sum=3"' "$label.out" || fail "$label: wrong output"
  grep -q '^paperlean-timing modules.fast packed=2 ' "$label.out" || fail "$label: the pack did not serve the import"
}
# (the same process view: the pack is used)
use same
# (another device number for every file, as on another host)
use otherdev LD_PRELOAD="$TMP_DIR/fakedev.so"
grep -q '^fake-dev: active' otherdev.out || fail "the LD_PRELOAD library did not change any device number"
true
