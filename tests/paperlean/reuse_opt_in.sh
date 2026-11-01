# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that `lean` reuses typeclass results and section variables only when a `paperlean` command
# asks for it, with `PAPERLEAN_REUSE=1`, which these commands set for the `lean` processes of their
# builds (`Lake.PaperLean.BuildEnv.leanEnv`), and neither `PAPERLEAN_EXACT` nor any other value: a
# plain `lean` runs Lean's path, also with the oracle (`PAPERLEAN_REUSE_ORACLE`), and so do the `lean`
# processes of a plain `lake build`. `paperlean build` reuses, in its own process and in a Lake of its
# own (`-R`), with the files of a plain `lake build`.

export XDG_CACHE_HOME="$(cd "$TMP_DIR" && pwd -P)/cache"
WS="$(cd "$TMP_DIR" && pwd -P)/ws"
mkdir -p "$WS"
cd "$WS"
cat > lakefile.toml <<'END'
name = "root"
defaultTargets = ["Root"]
[[lean_lib]]
name = "Root"
END
cat > Root.lean <<'END'
class C (α : Type) where
  x : α
instance : C Nat := ⟨0⟩
variable {α : Type} [C α] (a : α) (n : Fin (C.x (α := Nat) + 1))
theorem t1 : a = a := rfl
theorem t2 : (C.x : Nat) = C.x := rfl
theorem t3 : (C.x : Nat) = C.x := rfl
theorem t4 : a = a := rfl
END

# The columns of `PAPERLEAN_REUSE_STATS`: the typeclass results and the section variables reused,
# summed over the file's lines, and the searches and elaborations that went through the caches.
tc_reused() { awk -F '\t' '{ n += $2 } END { print n + 0 }' "$1"; }
tc_seen() { awk -F '\t' '{ n += $2 + $3 + $4 } END { print n + 0 }' "$1"; }
sv_reused() { awk -F '\t' '{ n += $6 } END { print n + 0 }' "$1"; }
sv_seen() { awk -F '\t' '{ n += $6 + $7 + $8 } END { print n + 0 }' "$1"; }
reuses() {
  [ "$(tc_reused "$1")" -ge 1 ] && [ "$(sv_reused "$1")" -ge 2 ] ||
    fail "$2 reused too little: $(cat "$1")"
}
no_reuse() {
  [ "$(tc_seen "$1")" = 0 ] && [ "$(sv_seen "$1")" = 0 ] || fail "$2 reused: $(cat "$1")"
}

PAPERLEAN_REUSE=1 PAPERLEAN_REUSE_STATS=asked.stats lean Root.lean || fail "lean failed"
reuses asked.stats "PAPERLEAN_REUSE=1 lean"
PAPERLEAN_REUSE_STATS=plain.stats lean Root.lean || fail "lean failed"
no_reuse plain.stats "plain lean"
PAPERLEAN_REUSE=0 PAPERLEAN_REUSE_STATS=zero.stats lean Root.lean || fail "lean failed"
no_reuse zero.stats "PAPERLEAN_REUSE=0 lean"
PAPERLEAN_REUSE=1 PAPERLEAN_EXACT=1 PAPERLEAN_REUSE_STATS=exact.stats lean Root.lean ||
  fail "lean failed"
no_reuse exact.stats "PAPERLEAN_EXACT=1 lean"
PAPERLEAN_REUSE_ORACLE=1 PAPERLEAN_REUSE_STATS=oracle.stats lean Root.lean || fail "lean failed"
no_reuse oracle.stats "lean with the oracle"

# `lake build` runs Lean's path; `paperlean build` reuses and gives the same files.
PAPERLEAN_REUSE_STATS="$WS/lake.stats" run lake build
no_reuse lake.stats "plain lake build"
outputs() { find .lake/build -name '*.olean*' -o -name '*.ilean' -o -name '*.c' | sort; }
for f in $(outputs); do mkdir -p "$TMP_DIR/ref/$(dirname "$f")"; cp "$f" "$TMP_DIR/ref/$f"; done
same_files() {
  for f in $(outputs); do cmp -s "$f" "$TMP_DIR/ref/$f" || fail "$f differs from plain lake's"; done
}
rm -rf .lake/build
PAPERLEAN_REUSE_STATS="$WS/build.stats" run lake paperlean build
reuses build.stats "paperlean build"
same_files
rm -rf .lake/build
PAPERLEAN_REUSE_STATS="$WS/spawned.stats" run lake paperlean build -R
reuses spawned.stats "paperlean build in a Lake of its own"
same_files
# (a plain Lake after these, whose environment a build in the process must not change)
rm -rf .lake/build lake2.stats
PAPERLEAN_REUSE_STATS="$WS/lake2.stats" run lake build
no_reuse lake2.stats "plain lake build"
