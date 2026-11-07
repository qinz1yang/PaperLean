# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests the summary at the end of `paperlean build` (`Lake.PaperLean.ReuseSummary`): what the `lean`
# processes of the build reused, and what they did not, with why and where, from the statistics that
# they write, in the build's own process and in a Lake of its own (`-R`): recordings that are not
# kept, each elaborator that is not on the whitelist with how often and where, section variables and
# typeclass results refused because of a change of what they depended on or another start, and what
# is left out of reuse altogether (trace options, proofs in the background, metavariables), which
# counts as computed in full. Nothing is said when
# nothing was compiled, by a plain `lake build`, or if the user asked for the statistics in a file; the
# file of a build does not stay. It also says which modules of the dependencies ran in the interpreter
# in the imports of the build, and why, which `lean` finds out an import at a time: for each reason that
# keeps a module from its native code, with what imports it, also of another package, in a library that
# lists only its root and in a package none of whose modules could be compiled; for modules that `prepare`
# did not look at, of targets that are not default ones, and new imports, also where no native library
# was prepared at all; never for modules that the build does not import, or that a plugin loaded; and
# for a module that imports treat differently, or if `lean` told only part of it, in as many words.
# What `prepare` found gives the reason only for the files that it read.
# `prepare` and `paperlean status` say what the prepared data leaves to the interpreter as a whole.

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
import Lean.Elab.ElabRules
open Lean Elab Term
elab "userProp%" : term => return mkConst ``True
class C (α : Type) where
  x : α
instance : C Nat := ⟨0⟩
section
variable (h : userProp%)
include h
theorem t1 : True := h
theorem t2 : True := h
theorem t3 : True := h
end
section
variable (n : Fin (C.x (α := Nat) + 1))
theorem u1 : n = n := rfl
theorem u2 : n = n := rfl
theorem u3 : n = n := rfl
end
END
check_summary() {
  check_out_contains "paperlean: compiled 1 module(s): reused"
  grep -Eq "the section variables of [2-9][0-9]* commands" "$CAPTURED.out.produced" ||
    fail "the summary does not say what was reused: $(cat "$CAPTURED.out.produced")"
  check_out_contains "paperlean: not reused, by reason, with the modules that have the most:"
  grep -Eq "^  3 section variables: not recordable: the elaborator .*UserProp.*, not on the whitelist \(Root\.lean:[0-9]+:[0-9]+\)$" "$CAPTURED.out.produced" ||
    fail "the summary does not say why and where: $(cat "$CAPTURED.out.produced")"
  ! ls .lake/paperlean-reuse-* > /dev/null 2>&1 || fail "the statistics of the build stayed"
}
no_summary() {
  ! grep -q "paperlean: compiled" "$CAPTURED.out.produced" ||
    fail "$1 said what was reused: $(cat "$CAPTURED.out.produced")"
}
capture lake build
no_summary "plain lake build"
rm -rf .lake/build
capture lake paperlean build
check_summary
# nothing compiled
capture lake paperlean build
no_summary "a build that compiled nothing"
rm -rf .lake/build
capture lake paperlean build -R
check_summary
rm -rf .lake/build
PAPERLEAN_REUSE_STATS="$WS/own.stats" capture lake paperlean build
no_summary "a build whose statistics the user asked for"
[ -s own.stats ] || fail "the user's file of statistics is empty"
# refusals, each with a number and a place: two user elaborators in one binder, each named with its
# number of elaborations, across namespaces, and a rare one, which no other reason hides; a change of what a recording read (an instance of a
# class of the binders); another start (options); and what is left out altogether
rm -rf .lake/build
cat > Root.lean <<'END'
import Lean.Elab.ElabRules
open Lean Elab Term
elab "ordinaryType%" : term => pure (mkConst ``Nat)
elab "otherType%" : term => pure (mkConst ``Nat)
elab "rareType%" : term => pure (mkConst ``Nat)
section
variable (n : rareType%)
theorem o1 : n = n := rfl
end
section
variable (n : ordinaryType%) (m : otherType%)
theorem t1 : n = n := rfl
namespace A
theorem t2 : n = n := rfl
end A
namespace B
theorem t3 : n = n := rfl
end B
end
class C (α : Type) where
  x : α
instance : C Nat := ⟨0⟩
section
variable (m : Fin (C.x (α := Nat) + 1))
theorem d1 : m = m := rfl
theorem d2 : m = m := rfl
instance (priority := high) : C Nat := ⟨0⟩
theorem d3 : m = m := rfl
end
section
variable (k : Fin (C.x (α := Nat) + 2))
theorem s1 : k = k := rfl
set_option pp.proofs true in
theorem s2 : k = k := rfl
end
section
variable (j : Fin (C.x (α := Nat) + 3))
set_option trace.Meta.synthInstance true in
theorem e1 : j = j := rfl
end
theorem b1 : (C.x : Nat) = C.x := by
  have : Inhabited (Fin 3) := inferInstance
  rfl
END
capture lake paperlean build
reason() {
  grep -Eq "^  $1 \(Root\.lean:[0-9]+:[0-9]+\)$" "$CAPTURED.out.produced" ||
    fail "the summary does not say: $1: $(cat "$CAPTURED.out.produced")"
}
reason "3 section variables: not recordable: the elaborator .*OrdinaryType.*, not on the whitelist"
reason "3 section variables: not recordable: the elaborator .*OtherType.*, not on the whitelist"
# (of however few elaborations, among the many reasons of this file)
reason "1 section variables: not recordable: the elaborator .*RareType.*, not on the whitelist"
reason "1 section variables: a change of the extension .*instanceExtension"
reason "1 section variables: another start \\(.*options\\)"
reason "[0-9]+ section variables: trace options or diagnostics"
reason "[0-9]+ typeclass results: trace options or diagnostics"
reason "[0-9]+ typeclass results: not on the thread that elaborates commands in order, e.g. in a proof"
reason "[0-9]+ typeclass results: metavariables in the problem or in its context"
# what is left out counts as computed in full: the section of the trace options is one of the
# elaborations, and the proof's and the others' searches are among the searches
grep -Eq "the section variables of [0-9]+ commands; [0-9]+ searches and [0-9]+ elaborations" "$CAPTURED.out.produced" ||
  fail "the summary has no totals: $(cat "$CAPTURED.out.produced")"
# ... and another namespace, for a read that a recording made, and a name that resolves otherwise
rm -rf .lake/build
cat > Root.lean <<'END'
import Lean.Elab.ElabRules
section
variable (n : with_decl_name% ?foo Nat)
theorem w1 : n = n := rfl
namespace A
theorem w2 : n = n := rfl
end A
end
def T := Nat
section
variable (n : T)
theorem r1 : n = n := rfl
theorem r2 : n = n := rfl
def A.T := Int
namespace A
theorem r3 : n = n := rfl
end A
end
END
capture lake paperlean build
reason "1 section variables: another namespace or other open declarations, which with_decl_name may read"
reason "1 section variables: a name that resolves otherwise now"

# What runs in the interpreter, by each reason that keeps a module from its native code, and what
# imports it, also of another package. All of it is prepared once, which takes long.
mkdir -p "$WS/sum/Dep" "$WS/top/Top" "$WS/plain/Plain" "$WS/ext/Ext" "$WS/gone" "$WS/ord/Ord"
cat > sum/lakefile.toml <<'END'
name = "sumdep"
defaultTargets = ["Dep"]
[[lean_lib]]
name = "Dep"
globs = ["Dep.+"]
# (built only as the root package imports it)
[[lean_lib]]
name = "Extra"
END
cat > sum/Dep/Base.lean <<'END'
def table : Array Nat := #[1, 2, 3]
def typo : Nat := table[7]!
def base (n : Nat) := n + 1
END
printf 'import Dep.Base\ndef mid (n : Nat) := base n\n' > sum/Dep/Mid.lean
printf 'def alone (n : Nat) := n\n' > sum/Dep/Alone.lean
printf 'def extra (n : Nat) := n\n' > sum/Extra.lean
# A library as most packages have it: only its root in `globs` by default, the rest by its imports.
cat > plain/lakefile.toml <<'END'
name = "plaindep"
defaultTargets = ["Plain"]
[[lean_lib]]
name = "Plain"
END
printf 'import Plain.Mid\ndef plainTop (n : Nat) := plainMid n\n' > plain/Plain.lean
printf 'import Plain.Base\ndef plainMid (n : Nat) := plainBase n\n' > plain/Plain/Mid.lean
cat > plain/Plain/Base.lean <<'END'
def plainTable : Array Nat := #[1, 2, 3]
def plainTypo : Nat := plainTable[7]!
def plainBase (n : Nat) := n + 1
END
# What the module declares.
cat > ext/lakefile.toml <<'END'
name = "extdep"
defaultTargets = ["Ext"]
[[lean_lib]]
name = "Ext"
globs = ["Ext.+"]
END
printf '@[extern "review_external_base"] def extBase (n : Nat) : Nat := n + 1\n' > ext/Ext/Base.lean
printf 'import Ext.Base\ndef extUp (n : Nat) := extBase n\n' > ext/Ext/Up.lean
printf 'builtin_initialize extRef : IO.Ref Nat ← IO.mkRef 0\n' > ext/Ext/Builtin.lean
cat > ext/Ext/Both.lean <<'END'
module
meta initialize pure ()
initialize pure ()
public def both (n : Nat) : Nat := n + 1
END
# A package none of whose modules could be compiled.
cat > gone/lakefile.toml <<'END'
name = "gonedep"
defaultTargets = ["Gone"]
[[lean_lib]]
name = "Gone"
END
printf 'def gone (n : Nat) := n\n' > gone/Gone.lean
# A package that Lake loads as a plugin, of which `prepare` makes a library too, and what imports it.
mkdir -p "$WS/precomp/Precomp" "$WS/preuser"
cat > precomp/lakefile.toml <<'END'
name = "precompdep"
defaultTargets = ["Precomp"]
[[lean_lib]]
name = "Precomp"
precompileModules = true
END
# (the library rejects this one, for what it declares and for its constant, which native initializers
# evaluate, so that the output shows whose code ran)
cat > precomp/Precomp/Rejected.lean <<'END'
builtin_initialize precompRef : IO.Ref Nat ← IO.mkRef 7
def precompBase (n : Nat) := n
def unusedPrecomp : Nat := dbgTrace "precomp probe evaluated" fun _ => 1
END
printf 'import Precomp.Rejected\ndef precomp (n : Nat) := precompBase n\n' > precomp/Precomp.lean
cat > preuser/lakefile.toml <<'END'
name = "preuserdep"
defaultTargets = ["PreUser"]
[[require]]
name = "precompdep"
path = "../precomp"
[[lean_lib]]
name = "PreUser"
END
printf 'import Precomp\ndef preUser (n : Nat) := precomp n\n' > preuser/PreUser.lean
cat > top/lakefile.toml <<'END'
name = "topdep"
defaultTargets = ["Top"]
[[require]]
name = "sumdep"
path = "../sum"
[[require]]
name = "gonedep"
path = "../gone"
[[lean_lib]]
name = "Top"
globs = ["Top.+"]
END
printf 'import Dep.Mid\ndef topFn (n : Nat) := mid n\n' > top/Top/Up.lean
printf 'import Gone\ndef over (n : Nat) := gone n\n' > top/Top/Over.lean
# An order of imports in which a compile-time initializer would come before those of what it calls.
cat > ord/lakefile.toml <<'END'
name = "orddep"
defaultTargets = ["Ord"]
[[lean_lib]]
name = "Ord"
globs = ["Ord.+"]
# (reached only from a target of the root package that `lake build` does not build)
[[lean_lib]]
name = "Side"
[[lean_lib]]
name = "Many"
END
mkdir -p ord/Side ord/Many
printf 'import Side.Base\ndef side (n : Nat) := sideBase n\n' > ord/Side.lean
printf 'def sideBase (n : Nat) := n\n' > ord/Side/Base.lean
printf 'import Side.Base\ndef uses (n : Nat) := sideBase n\n' > ord/Ord/Uses.lean
# (not built when `prepare` runs)
printf 'def fresh (n : Nat) := n\n' > ord/Ord/Fresh.lean
for i in $(seq 120); do
  echo "def many$i : Nat := $i" > ord/Many/M$i.lean
  echo "import Many.M$i" >> ord/Many.lean
done
cat > ord/Ord/P1.lean <<'END'
module
public structure P1S where
  x : Nat
  h : x = x := by rfl
@[noinline] public meta def p1f (n : Nat) : Nat := n + 1
END
cat > ord/Ord/P2.lean <<'END'
module
import Ord.P1
public structure P2S where
  y : Nat
  h : y = y := by rfl
END
cat > ord/Ord/P3.lean <<'END'
module
import Ord.P1
meta def p3c : Nat := p1f 2
public def p3 : Nat := 3
END
# The `meta` code of a module imported for run time only uses what its runtime initializer initializes,
# which does not run then, and a module that imports it.
cat > ord/Ord/MB.lean <<'END'
module
public meta section
def dein (n : Nat) (s : String) : String := s.replace (String.ofList ('\n' :: List.replicate n ' ')) " "
public def mbLen (s : String) : Nat := (dein 2 s).length
end
END
cat > ord/Ord/MBUp.lean <<'END'
module
public import Ord.MB
public meta def mbUp (s : String) : Nat := mbLen s + 1
END
cat > UseB.lean <<'END'
module
import Ord.MBUp
#eval mbUp "a\n  b"
END
cat > UseP.lean <<'END'
module
import Ord.P2
import Ord.P3
import Ord.P1
def s : P2S := { y := 3 }
#check p3
#eval s.y
END
cat > lakefile.toml <<'END'
name = "root"
defaultTargets = ["Root", "UseP", "UseB"]
# (not built by `lake build`)
[[lean_lib]]
name = "Other"
[[lean_lib]]
name = "UseMany"
[[lean_lib]]
name = "UsePre"
[[lean_lib]]
name = "UseAlone"
[[require]]
name = "topdep"
path = "top"
[[require]]
name = "plaindep"
path = "plain"
[[require]]
name = "extdep"
path = "ext"
[[require]]
name = "orddep"
path = "ord"
[[require]]
name = "preuserdep"
path = "preuser"
[[lean_lib]]
name = "Root"
[[lean_lib]]
name = "UseP"
[[lean_lib]]
name = "UseB"
END
cat > Root.lean <<'END'
import Top.Up
import Top.Over
import Dep.Alone
import Extra
import Plain
import Ext.Up
import Ext.Builtin
import Ext.Both
def x := topFn 1
END
mkdir -p Other
printf 'def helper (n : Nat) := n\n' > Other/Helper.lean
cat > Other.lean <<'END'
import Other.Helper
import Side
import Ord.Uses
#eval side (helper 1)
END
printf 'import Many\n#eval many1\n' > UseMany.lean
printf 'import PreUser\n#eval preUser 1\n' > UsePre.lean
printf 'import Dep.Alone\n' > UseAlone.lean
run lake update
run lake build
run lake build Other UseMany UsePre UseAlone
rm gone/.lake/build/ir/Gone.c
capture lake paperlean prepare
check_out_contains "sumdep: 3 modules, 1 left out, 2 interpreted unless a plugin loads them"
check_out_contains "plaindep: 3 modules, 3 interpreted unless a plugin loads them"
check_out_contains "extdep: 3 modules, 1 left out, 3 interpreted unless a plugin loads them"
check_out_contains "gonedep: 0 modules, 1 left out"
check_out_contains "topdep: 2 modules, 2 interpreted unless a plugin loads them"
check_out_contains "orddep: 6 modules, 1 interpreted unless a plugin loads them, 123 outside its default libraries"
check_out_contains "precompdep: 2 modules, 1 rejected, whose code a plugin loads"
check_out_contains "preuserdep: 1 modules, 1 interpreted unless a plugin loads them"
check_out_contains "e.g. Dep.Base: \`typo\` panics"
check_out_contains "e.g. Plain.Base: \`plainTypo\` panics"
interpreted() { # <module>: <reason>
  check_out_contains "$1 runs in the interpreter where no plugin loads it: $2"
}
check_status() {
  capture lake paperlean status
  interpreted Dep.Base "\`typo\` panics"
  interpreted Dep.Mid "it imports one that does"
  interpreted Top.Up "it imports one that does"
  interpreted Extra "it is in no default library of its package"
  # (below the root of a library, which `globs` do not list)
  interpreted Plain.Base "\`plainTypo\` panics"
  interpreted Plain.Mid "it imports one that does"
  interpreted Plain "it imports one that does"
  interpreted Ext.Base "it declares the \`@[extern]\` function review_external_base"
  interpreted Ext.Up "its C uses inputs outside the relocatable generated-C profile"
  interpreted Ext.Builtin "it has \`builtin_initialize\` declarations"
  interpreted Ext.Both "it has \`[init]\` declarations of both phases"
  interpreted Gone "no .c"
  interpreted Top.Over "it imports one that does"
  # (no build of the root package's default targets imports them)
  check_out_contains "Side.Base is in no default library of its package, so it runs in the interpreter where no plugin loads it"
  interpreted Ord.Uses "it imports one that does"
  # (a module that the library rejects is not interpreted if a plugin loads it, nor is what it imports)
  check_out_contains "Precomp.Rejected loads as a plugin, not from the prepared library: it has \`builtin_initialize\` declarations"
  ! grep -q "Precomp.Rejected runs in the interpreter\|Precomp runs in the interpreter" "$CAPTURED.out.produced" ||
    fail "status says that code that a plugin loads is interpreted"
  interpreted PreUser "it imports a module whose native code a plugin loaded, so its library's code is not used"
}
check_status
# what `lean` then does is what was said
printf 'import Plain\n#eval plainTop 1\n' > UsePlain.lean
capture env PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean UsePlain.lean
check_out_contains "paperlean-timing native libs=0 modules=0 meta=0 verified=3 importsNotUsed=2"
printf 'import Ext.Up\n' > UseExt.lean
capture env PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean UseExt.lean
check_out_contains "paperlean-timing native libs=0 modules=0 meta=0 verified=1 importsNotUsed=0"
echo 'def y := 2' >> Root.lean
check_root() {
  # (only what `Root` imports; a `meta import` of `Ext.Both` would use its code)
  check_out_contains "paperlean: 12 dependency module(s) run in the interpreter, with the same results but slower:"
  check_out_contains "  Dep.Base: \`typo\` panics"
  check_out_contains "  Plain.Base: \`plainTypo\` panics"
  check_out_contains "  Ext.Base: it declares the \`@[extern]\` function review_external_base"
  # (the first build compiled it again, for its `.c`, so that `prepare`'s `no .c` no longer holds)
  check_out_contains "  Gone: no prepared native library has it"
  check_out_contains "  Extra: it is in no default library of its package"
  check_out_contains "  and 5 that import one that does"
  check_out_contains "paperlean: 1 dependency module(s) run in the interpreter in some imports:"
  check_out_contains "  Ext.Both: it has \`[init]\` declarations of both phases"
}
capture lake paperlean build
check_root
# nothing compiled, nothing used
capture lake paperlean build
! grep -q "run in the interpreter" "$CAPTURED.out.produced" || fail "a build that compiled nothing spoke of the interpreter"
# What `prepare` found is no concern of a build that imports none of it.
printf '\n-- changed\n' >> UseAlone.lean
capture lake paperlean build UseAlone
check_out_contains "paperlean: compiled 1 module(s)"
! grep -q "run in the interpreter" "$CAPTURED.out.produced" || fail "a build was told of modules that it does not import"
# Statistics that the user asked for in a file stay theirs, and take nothing from what is said here.
echo 'def z := 3' >> Root.lean
PAPERLEAN_REUSE_STATS="$WS/own2.stats" capture lake paperlean build
no_summary "a build whose statistics the user asked for"
check_root
[ -s own2.stats ] || fail "the user's file of statistics is empty"
! grep -q "^native" own2.stats || fail "the user's file of statistics holds what was meant for the summary"
# What depends on an import, which `prepare` cannot tell: `lean` says, for the modules of the import.
echo '-- changed' >> UseP.lean
echo '-- changed' >> UseB.lean
capture env PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean UseP.lean
check_out_contains "initOrder=1"
capture env PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean UseB.lean
check_out_contains "importsNotUsed=1 initOrder=0 other=1"
capture lake paperlean build
check_out_contains "paperlean: 3 dependency module(s) run in the interpreter in some imports:"
check_out_contains "  Ord.P3: its initializers would run in another order"
check_out_contains "  Ord.MB: an import does not run its runtime initializer, which its \`meta\` code needs"
check_out_contains "  and 1 that import one that does"
# What is outside what `prepare` looked at: dependency modules that a target outside the default ones
# imports, but not that target's own modules, and the importers among the modules that have a library.
printf '\n-- changed\n' >> Other.lean
capture lake paperlean build Other
check_out_contains "paperlean: 3 dependency module(s) run in the interpreter, with the same results but slower:"
check_out_contains "  Side.Base: no prepared native library has it"
check_out_contains "  Side: no prepared native library has it"
! grep -q "Other.Helper" "$CAPTURED.out.produced" || fail "a module of the root package was reported"
# ... and an import that came after `prepare`
printf 'import Ord.Fresh\n' | cat - Other.lean > Other.new
mv Other.new Other.lean
capture lake paperlean build Other
check_out_contains "paperlean: 4 dependency module(s) run in the interpreter, with the same results but slower:"
check_out_contains "  Ord.Fresh: no prepared native library has it"
# ... of a size that the statistics of each `lean` do not hold in full
printf '\n-- changed\n' >> UseMany.lean
check_partly() {
  check_out_contains "paperlean: at least $1 dependency module(s) run in the interpreter in some imports:"
  check_out_contains "  and perhaps others: \`lean\` names the first 100 of an import"
  ! grep -q "with the same results but slower" "$CAPTURED.out.produced" || fail "a summary of a part said what holds of all"
}
capture lake paperlean build UseMany
check_partly 100
# Code that a plugin loaded is used, though a library has it too, but no library's code that calls it.
printf '\n-- changed\n' >> UsePre.lean
capture env PAPERLEAN_ACCELERATE=1 PAPERLEAN_IMPORT_TIMING=1 lake lean UsePre.lean
check_out_contains "importsNotUsed=1"
capture lake paperlean build UsePre
check_out_contains "precomp probe evaluated"
check_out_contains "paperlean: 1 dependency module(s) run in the interpreter in some imports:"
check_out_contains "  PreUser: it imports a module whose native code a plugin loaded, so its library's code is not used"
! grep -q "  Precomp: \|  Precomp.Rejected: " "$CAPTURED.out.produced" || fail "code that a plugin loaded was said to be interpreted"

# No prepared native library at all: `lean` is given none, and says the same. The default library of
# the dependency is not built, so `prepare` has nothing to compile; the other fixtures have libraries.
mkdir -p "$TMP_DIR/none/dep/Many" "$TMP_DIR/none/dep/Known" "$TMP_DIR/none/pre/Pre" "$TMP_DIR/none/Other"
cd "$TMP_DIR/none"
cat > dep/lakefile.toml <<'END'
name = "nonedep"
defaultTargets = ["D"]
[[lean_lib]]
name = "D"
[[lean_lib]]
name = "Extra"
[[lean_lib]]
name = "Many"
[[lean_lib]]
name = "Known"
[[lean_lib]]
name = "Late"
END
printf 'builtin_initialize dRef : IO.Ref Nat ← IO.mkRef 1\ndef d : Nat := 1\n' > dep/D.lean
printf 'def late : Nat := 1\n' > dep/Late.lean
# (more modules than an import tells of, all of which `prepare` names, as the root package imports them)
for i in $(seq 105); do
  echo "def known$i : Nat := $i" > dep/Known/M$i.lean
  echo "import Known.M$i" >> dep/Known.lean
done
# A dependency whose code Lake loads as a plugin. A constant runs its code only if native initializers
# run, which shows that the plugin's code is what is used.
cat > pre/lakefile.toml <<'END'
name = "nonepre"
defaultTargets = ["Pre"]
[[lean_lib]]
name = "Pre"
precompileModules = true
END
printf 'import Pre.Base\ndef pre (n : Nat) := preBase n\n' > pre/Pre.lean
cat > pre/Pre/Base.lean <<'END'
def preProbe : Nat := dbgTrace "pre probe evaluated" fun _ => 1
def preBase (n : Nat) := n
END
printf 'def extra (n : Nat) : Nat := n\n' > dep/Extra.lean
for i in $(seq 110); do
  echo "def many$i : Nat := $i" > dep/Many/M$i.lean
  echo "import Many.M$i" >> dep/Many.lean
done
cat > lakefile.toml <<'END'
name = "noneroot"
defaultTargets = ["Root"]
[[require]]
name = "nonedep"
path = "dep"
[[require]]
name = "nonepre"
path = "pre"
[[lean_lib]]
name = "Root"
[[lean_lib]]
name = "Other"
[[lean_lib]]
name = "UseMany"
[[lean_lib]]
name = "UsePre"
[[lean_lib]]
name = "UseKnown"
[[lean_lib]]
name = "UseD"
# (loads what it imports as plugins, which `prepare` of its dependency cannot tell)
[[lean_lib]]
name = "Loads"
precompileImports = true
END
printf 'import D\n' > UseD.lean
printf 'import D\n' > Loads.lean
printf 'import Known\ndef root : Nat := 1\n' > Root.lean
printf 'import Pre\nimport Extra\n#eval pre (extra 1)\n' > UsePre.lean
printf 'import Known\nimport Late\n#eval late\n' > UseKnown.lean
printf 'def helper (n : Nat) := n\n' > Other/Helper.lean
cat > Other.lean <<'END'
import Other.Helper
import Extra
#eval extra (helper 1)
#eval show IO Unit from do IO.println s!"asked: {(← IO.getEnv "PAPERLEAN_ROOT_PACKAGE").isSome}"
END
printf 'import Many\n#eval many1\n' > UseMany.lean
run lake update
run lake build Root Other UseMany UsePre UseKnown
# More dependency modules than an import tells of: what came after them (`Late`) is not named, and the
# summary must say that it may have left something out.
check_truncated() {
  printf '\n-- changed\n' >> UseKnown.lean
  capture lake paperlean build UseKnown
  check_partly 100
  ! grep -q "  Late: " "$CAPTURED.out.produced" || fail "the test does not test this: \`lean\` named all of them"
}
check_no_library() {
  printf '\n-- changed\n' >> Other.lean
  capture lake paperlean build Other
  check_out_contains "paperlean: 1 dependency module(s) run in the interpreter, with the same results but slower:"
  check_out_contains "  Extra: no prepared native library has it"
  check_out_contains "asked: true"
  ! grep -q "Other.Helper" "$CAPTURED.out.produced" || fail "a module of the root package was reported"
  printf '\n-- changed\n' >> UseMany.lean
  capture lake paperlean build UseMany
  check_partly 100
  # Code that a plugin loaded is no fallback; what has none next to it still is.
  printf '\n-- changed\n' >> UsePre.lean
  capture lake paperlean build UsePre
  check_out_contains "pre probe evaluated"
  check_out_contains "paperlean: 1 dependency module(s) run in the interpreter, with the same results but slower:"
  check_out_contains "  Extra: no prepared native library has it"
  ! grep -q "  Pre: \|  Pre.Base: " "$CAPTURED.out.produced" || fail "code that a plugin loaded was said to be interpreted"
}
capture lake paperlean prepare nonedep
check_out_contains "nonedep: 0 modules, 106 left out, 113 outside its default libraries"
capture lake paperlean status
check_out_contains "Extra is in no default library of its package, so it runs in the interpreter where no plugin loads it"
has_library() { tr -d ' \n' < .lake/paperlean/env.json | grep -q '"native":\["'; }
! has_library || fail "the test does not test this: a library was prepared"
check_no_library
check_truncated
# ... and with native libraries left out on purpose
capture lake paperlean clean
capture lake paperlean prepare nonedep nonepre --no-native
check_no_library
# (`prepare` then looks at no module, so that it told of none of these)
printf '\n-- changed\n' >> UseKnown.lean
capture lake paperlean build UseKnown
check_partly 100
check_out_contains "  Known.M1: no prepared native library has it"
# ... and where a library is in use, which `lean` reaches on another path
capture lake paperlean clean
run lake build D UseD Loads
capture lake paperlean prepare
check_out_contains "nonedep: 1 modules, 106 left out, 1 interpreted unless a plugin loads them, 113 outside its default libraries"
check_out_contains "nonepre: 2 modules, 1 rejected, whose code a plugin loads"
has_library || fail "the test does not test this: no library was prepared"
check_truncated
# What each import did, which `prepare` cannot tell: `D` is interpreted by the target that does not load
# it as a plugin, and no more than that of the modules that `prepare` found is said to either.
check_use_d() {
  check_out_contains "paperlean: 1 dependency module(s) run in the interpreter$1"
  check_out_contains "  D: it has \`builtin_initialize\` declarations"
  ! grep -q "Known" "$CAPTURED.out.produced" || fail "a build was told of modules that it does not import"
}
printf '\n-- changed\n' >> UseD.lean
capture lake paperlean build UseD
check_use_d ", with the same results but slower:"
printf '\n-- changed\n' >> Loads.lean
capture lake paperlean build Loads
! grep -q "run in the interpreter" "$CAPTURED.out.produced" || fail "code that a plugin loaded was said to be interpreted"
# ... and what one import loaded does not cancel what another did not.
printf '\n-- changed\n' >> UseD.lean
printf '\n-- changed\n' >> Loads.lean
capture lake paperlean build UseD Loads
check_use_d " in some imports:"
! grep -q "with the same results but slower" "$CAPTURED.out.produced" || fail "what differs by import was said of all of them"
# Without prepared data the first line says that, and `lean` is not asked for more, which takes time.
capture lake paperlean clean
printf '\n-- changed\n' >> Other.lean
capture lake paperlean build Other
check_out_contains "PaperLean prepared data: none prepared"
check_out_contains "asked: false"
! grep -q "run in the interpreter" "$CAPTURED.out.produced" || fail "the summary spoke of data that does not exist"

# More modules that plugins load than an import tells of: those are no fallback, named or not, and a
# fallback next to them is not said to be all that the build did with its module. A package without
# its library is named only to a build that meets it.
mkdir -p "$TMP_DIR/many/dep/Rej" "$TMP_DIR/many/bad"
cd "$TMP_DIR/many"
cat > dep/lakefile.toml <<'END'
name = "manydep"
defaultTargets = ["Rej"]
[[lean_lib]]
name = "Rej"
END
for i in $(seq 101); do
  echo "builtin_initialize rej$i : IO.Ref Nat ← IO.mkRef $i" > dep/Rej/M$i.lean
  echo "import Rej.M$i" >> dep/Rej.lean
done
cat > bad/lakefile.toml <<'END'
name = "baddep"
defaultTargets = ["Bad"]
[[lean_lib]]
name = "Bad"
moreLinkArgs = ["-lpaperlean-no-such-library"]
END
printf 'def bad : Nat := 1\n' > bad/Bad.lean
cat > lakefile.toml <<'END'
name = "manyroot"
[[require]]
name = "manydep"
path = "dep"
[[require]]
name = "baddep"
path = "bad"
[[lean_lib]]
name = "UseLast"
[[lean_lib]]
name = "UseBad"
[[lean_lib]]
name = "LoadsAll"
precompileImports = true
END
printf 'import Rej.M101\n' > UseLast.lean
printf 'import Bad\n' > UseBad.lean
printf 'import Rej\n' > LoadsAll.lean
run lake update
run lake build UseLast UseBad LoadsAll
capture lake paperlean prepare
check_out_contains "the native library of baddep could not be built"
has_library || fail "the test does not test this: no library was prepared"
printf '\n-- changed\n' >> LoadsAll.lean
capture lake paperlean build LoadsAll
check_out_contains "paperlean: compiled 1 module(s)"
! grep -q "run in the interpreter" "$CAPTURED.out.produced" || fail "code that a plugin loaded was said to be interpreted"
printf '\n-- changed\n' >> UseLast.lean
capture lake paperlean build UseLast
check_out_contains "paperlean: 1 dependency module(s) run in the interpreter, with the same results but slower:"
check_out_contains "  Rej.M101: it has \`builtin_initialize\` declarations"
! grep -q "no native library of" "$CAPTURED.out.produced" || fail "a build was told of a package that it does not import"
printf '\n-- changed\n' >> LoadsAll.lean
printf '\n-- changed\n' >> UseLast.lean
capture lake paperlean build LoadsAll UseLast
check_partly 1
check_out_contains "  Rej.M101: it has \`builtin_initialize\` declarations"
printf '\n-- changed\n' >> UseBad.lean
capture lake paperlean build UseBad
check_out_contains "paperlean: no native library of baddep: not built ("
check_out_contains "paperlean: 1 dependency module(s) run in the interpreter, with the same results but slower:"
check_out_contains "  Bad: no prepared native library has it"

# What `prepare` found is said only of the files that it read. After a change the loader's reason stands,
# for a module that the library rejected, for one that imported it, and for two that it left out: one
# whose `.c` the build wrote again, and one that the control shows with the reason of `prepare`.
mkdir -p "$TMP_DIR/stale/dep/Stale"
cd "$TMP_DIR/stale"
cat > dep/lakefile.toml <<'END'
name = "staledep"
defaultTargets = ["Stale"]
[[lean_lib]]
name = "Stale"
[[lean_lib]]
name = "Outside"
END
printf 'import Stale.Up\nimport Stale.Gone\n' > dep/Stale.lean
printf 'def outside : Nat := 1\n' > dep/Outside.lean
printf 'builtin_initialize staleRef : IO.Ref Nat ← IO.mkRef 1\ndef staleBase : Nat := 1\n' > dep/Stale/Base.lean
printf 'import Stale.Base\ndef staleUp : Nat := staleBase\n' > dep/Stale/Up.lean
printf 'def staleGone : Nat := 1\n' > dep/Stale/Gone.lean
cat > lakefile.toml <<'END'
name = "staleroot"
defaultTargets = ["Root"]
[[require]]
name = "staledep"
path = "dep"
[[lean_lib]]
name = "Root"
END
printf 'import Stale.Up\nimport Stale.Gone\nimport Outside\n' > Root.lean
run lake update
run lake build
rm dep/.lake/build/ir/Stale/Gone.c
capture lake paperlean prepare
printf '\n-- changed\n' >> Root.lean
capture lake paperlean build
check_out_contains "paperlean: 4 dependency module(s) run in the interpreter, with the same results but slower:"
check_out_contains "  Stale.Base: it has \`builtin_initialize\` declarations"
check_out_contains "  Outside: it is in no default library of its package"
check_out_contains "  and 1 that import one that does"
[ -f dep/.lake/build/ir/Stale/Gone.c ] || fail "the test does not test this: the build did not write the \`.c\`"
check_out_contains "  Stale.Gone: no prepared native library has it"
! grep -q "no \.c" "$CAPTURED.out.produced" || fail "what \`prepare\` found of other files was said of these"
printf 'def staleBase : Nat := 1\n' > dep/Stale/Base.lean
printf 'def outside : Nat := 2\n' > dep/Outside.lean
capture lake paperlean build
check_out_contains "paperlean: 4 dependency module(s) run in the interpreter, with the same results but slower:"
check_out_contains "  Stale.Base: its files are not those that \`paperlean prepare\` read"
check_out_contains "  Stale.Up: its files are not those that \`paperlean prepare\` read"
check_out_contains "  Outside: no prepared native library has it"
! grep -q "builtin_initialize\|no default library\|that import one that does" "$CAPTURED.out.produced" ||
  fail "what \`prepare\` found of other files was said of these"
