# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that `paperlean prepare` and `paperlean clean` of some packages, which pack (and bind) the current
# files of the others again and keep their native libraries, keep what `prepare` found of those packages only for
# the files that it found that of. The reason of a module that changed since, and that it imports one that
# runs in the interpreter, are gone from the end of a build and from `paperlean status`, and the loader's
# reason stands; so is the reason why a package has no library. A module that did not change keeps
# its reason, also through several such runs and in a package outside the workspace, and a `prepare` of the
# package itself finds out anew. Without the pack that it was found with, nothing is known of the files.
# What depends on a package's configuration is not said against what its lakefile says now.
# Why a package has no library is said only of what that attempt tried: its modules, their files, its link
# arguments and the packages it depends on, whether files were edited or deleted or only the lakefile
# changed, with or without a partial run between, and `status` checks what it says of modules likewise.
# All that `prepare` found of a package goes if the configuration of the package or of a package it depends
# on changes, what it compiles and links with or the compiler included, as soon as that does, before
# anything is built: how many modules its library holds is all that is left to say of it.

export XDG_CACHE_HOME="$(cd "$TMP_DIR" && pwd -P)/cache"
ROOT="$(cd "$TMP_DIR" && pwd -P)"
mkdir -p "$ROOT/ws/dep/Dep" "$ROOT/far"
for p in other bad needy pre plug user nopic flag; do mkdir "$ROOT/ws/$p"; done
cd "$ROOT/ws"
cat > dep/lakefile.toml <<'END'
name = "dep"
defaultTargets = ["Dep"]
[[lean_lib]]
name = "Dep"
[[lean_lib]]
name = "Outside"
END
printf 'import Dep.Up\nimport Dep.Gone\nimport Dep.Left\nimport Dep.Stays\n' > dep/Dep.lean
printf '@[extern "lean_paperlean_test_missing"] opaque missing : Nat → Nat\n' > dep/Dep/Ext.lean
printf 'import Dep.Ext\ndef stays (n : Nat) : Nat := missing n + 2\n' > dep/Dep/Stays.lean
printf 'import Dep.Base\ndef up : Nat := base\n' > dep/Dep/Up.lean
printf 'name = "other"\ndefaultTargets = ["Other"]\n[[lean_lib]]\nname = "Other"\n' > other/lakefile.toml
printf 'def other : Nat := 1\n' > other/Other.lean
printf 'def bad : Nat := 1\n' > bad/Bad.lean
printf 'def badAside : Nat := 1\n' > bad/BadAside.lean
printf 'def needy : Nat := 1\n' > needy/Needy.lean
printf 'name = "pre"\ndefaultTargets = ["Pre"]\n[[lean_lib]]\nname = "Pre"\nprecompileModules = true\n' > pre/lakefile.toml
printf 'name = "plug"\ndefaultTargets = ["Plug"]\n[[require]]\nname = "pre"\npath = "../pre"\n[[lean_lib]]\nname = "Plug"\n' > plug/lakefile.toml
printf 'import Pre\ndef plug : Nat := pre\n' > plug/Plug.lean
printf 'def nopic : List Nat := [1, 2, 3]\n' > nopic/Nopic.lean
printf 'def flag : Nat := 1\n' > flag/Flag.lean
printf 'name = "user"\ndefaultTargets = ["User"]\n[[require]]\nname = "dep"\npath = "../dep"\n[[lean_lib]]\nname = "User"\n' > user/lakefile.toml
printf 'import Dep.Gone\ndef user : Nat := gone\n' > user/User.lean
cat > ../far/lakefile.toml <<'END'
name = "far"
defaultTargets = ["Far"]
[[lean_lib]]
name = "Far"
[[lean_lib]]
name = "FarOut"
[[lean_lib]]
name = "FarAside"
END
printf 'def far : Nat := 1\n' > ../far/Far.lean
printf 'def farOut : Nat := 1\n' > ../far/FarOut.lean
cat > lakefile.toml <<'END'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "dep"
path = "dep"
[[require]]
name = "other"
path = "other"
[[require]]
name = "bad"
path = "bad"
[[require]]
name = "needy"
path = "needy"
[[require]]
name = "pre"
path = "pre"
[[require]]
name = "plug"
path = "plug"
[[require]]
name = "nopic"
path = "nopic"
[[require]]
name = "flag"
path = "flag"
[[require]]
name = "user"
path = "user"
[[require]]
name = "far"
path = "../far"
[[lean_lib]]
name = "Root"
[[lean_lib]]
name = "UsePre"
END
printf 'import Pre\n' > UsePre.lean

missing='it refers to lean_paperlean_test_missing, which nothing defines'
builtin='it has `builtin_initialize` declarations'
outside='it is in no default library of its package'
runs='runs in the interpreter where no plugin loads it:'
outdated='what `paperlean prepare` found of it may no longer hold'
loader='no prepared native library has it'
read='its files are not those that `paperlean prepare` read'
unsupported='PaperLean does not support'
generic='not built (its files or configuration may have changed since it failed)'
linker='not built (external command'
changed='modules (its configuration or a dependency'"'"'s may have changed since)'
unless_plugin='a plugin loaded, so its library'"'"'s code is not used'
# (what position-dependent code cannot link with, and a compiler cannot take)
nopic_args='moreLeancArgs = ["-fno-PIC"]
moreLinkArgs = ["-Wl,-z,text"]
'
flag_args='moreLeancArgs = ["--no-such-flag"]
'

bad_lakefile() { # [TOML of its library `Bad`]
  printf 'name = "bad"\ndefaultTargets = ["Bad", "Collides"]\n[[lean_lib]]\nname = "Bad"\n%s[[lean_lib]]\nname = "Collides"\n[[lean_lib]]\nname = "BadAside"\n' "${1:-}" > bad/lakefile.toml
}
needy_lakefile() { # [TOML of its requirement]
  printf 'name = "needy"\ndefaultTargets = ["Needy"]\n%s[[lean_lib]]\nname = "Needy"\n' "${1:-}" > needy/lakefile.toml
}
needs_bad='[[require]]
name = "bad"
path = "../bad"
'
lib_lakefile() { # <package> <library> [TOML of the library]
  printf 'name = "%s"\ndefaultTargets = ["%s"]\n[[lean_lib]]\nname = "%s"\n%s' "$1" "$2" "$2" "${3:-}" > "$1/lakefile.toml"
}
root_imports() { # [the import of `Collides`] (in the order of the summary, which names 10)
  printf 'import Flag\nimport FarOut\nimport Dep\nimport Outside\nimport Other\nimport Bad\n%simport Far\nimport User\nimport Needy\nimport Nopic\n' "${1-import Collides
}" > Root.lean
}
# The modules as `prepare` finds them, and what is left out of `dep`'s library.
first_state() {
  bad_lakefile
  needy_lakefile "$needs_bad"
  lib_lakefile nopic Nopic "$nopic_args"
  lib_lakefile flag Flag "$flag_args"
  root_imports
  printf 'import Dep.Up\nimport Dep.Gone\nimport Dep.Left\nimport Dep.Stays\n' > dep/Dep.lean
  printf 'def farAside : Nat := 1\n' > ../far/FarAside.lean
  printf 'builtin_initialize baseRef : IO.Ref Nat ← IO.mkRef 1\ndef base : Nat := 1\n' > dep/Dep/Base.lean
  printf 'def gone : Nat := 1\n' > dep/Dep/Gone.lean
  printf 'import Dep.Ext\ndef left (n : Nat) : Nat := missing n + 1\n' > dep/Dep/Left.lean
  printf 'def outside : Nat := 1\n' > dep/Outside.lean
  printf 'import Lean\nopen Lean\n@[export lean_name_append_after] def shadow (_n : Name) (_s : String) : Name := `shadowed\n' > bad/Collides.lean
  printf 'builtin_initialize preRef : IO.Ref Nat ← IO.mkRef 1\ndef pre : Nat := 1\n' > pre/Pre.lean
  run lake build Root UsePre FarAside Plug
  [ "${1:-}" != "no-c" ] || rm dep/.lake/build/ir/Dep/Gone.c
  capture lake paperlean prepare
}
# Each of them changes, is built by Lake, and `.c` of `Gone` is back.
second_state() {
  printf 'def base : Nat := 2\n' > dep/Dep/Base.lean
  printf 'def gone : Nat := 2\n' > dep/Dep/Gone.lean
  printf 'import Dep.Ext\ndef left (n : Nat) : Nat := missing n + 3\n' > dep/Dep/Left.lean
  printf 'def outside : Nat := 2\n' > dep/Outside.lean
  printf 'def shadow : Nat := 2\n' > bad/Collides.lean
  printf 'def pre : Nat := 2\n' > pre/Pre.lean
  run lake build Root UsePre Plug
  [ -s dep/.lake/build/ir/Dep/Gone.c ] || fail "the test does not test this: no \`.c\` of Dep.Gone"
}
compile() {
  printf '\n-- changed\n' >> Root.lean
  capture lake paperlean build
}
lacks() { # <fixed string>: the last output does not have it
  ! grep -Fq -- "$1" "$CAPTURED.out.produced" || fail "the output has '$1', of other files"
}
# What holds of the modules that did not change, in all of the runs below.
unchanged_build() {
  check_out_contains "  Dep.Stays: $missing"
  check_out_contains "  FarOut: $outside"
}
unchanged_status() {
  check_out_contains "Dep.Stays $runs $missing"
  check_out_contains "FarOut $runs $outside"
}

# With nothing changed everything stays, whatever is packed again.
found_all() {
  compile
  unchanged_build
  check_out_contains "  Dep.Base: $builtin"
  check_out_contains "  Dep.Left: $missing"
  check_out_contains "  Outside: $outside"
  check_out_contains "that import one that does"
  check_out_contains "paperlean: no native library of bad: not built ($unsupported"
  check_out_contains "paperlean: no native library of needy: not built (bad has no native library)"
  check_out_contains "  Flag: compile failed"
  capture lake paperlean status
  unchanged_status
  check_out_contains "native library of bad: not built ($unsupported"
  check_out_contains "native library of pre: 1 modules, 1 rejected, whose code a plugin loads"
  check_out_contains "native library of plug: 1 modules, 1 interpreted unless a plugin loads them"
  check_out_contains "Plug $runs it imports a module whose native code $unless_plugin"
  check_out_contains "Flag $runs compile failed"
  check_out_contains "Dep.Base $runs $builtin"
  check_out_contains "Dep.Left $runs $missing"
  check_out_contains "Dep.Up $runs it imports one that does"
  check_out_contains "Pre loads as a plugin, not from the prepared library: $builtin"
  check_out_contains "FarAside is in no default library of its package"
  lacks "may no longer hold"
  lacks "may have changed"
}
bad_lakefile
needy_lakefile "$needs_bad"
lib_lakefile nopic Nopic "$nopic_args"
lib_lakefile flag Flag "$flag_args"
root_imports
printf 'import Dep.Up\nimport Dep.Gone\nimport Dep.Left\nimport Dep.Stays\n' > dep/Dep.lean
run lake update
first_state
found_all
capture lake paperlean prepare other
found_all
capture lake paperlean clean other
found_all
capture lake paperlean prepare other
found_all
# Another compiler is another input, of all that was found, and while it is the other: nothing is kept.
capture env LEAN_CC="$ROOT/another-cc" lake paperlean status
check_out_contains "native library of bad: $generic"
check_out_contains "Dep.Stays $runs $outdated"
capture lake paperlean status
check_out_contains "native library of bad: not built ($unsupported"
check_out_contains "Dep.Stays $runs $missing"

# After a change, what `prepare` found of the files before says nothing more.
told_of_the_files() {
  compile
  unchanged_build
  check_out_contains "  Dep.Gone: $loader"
  check_out_contains "  Dep.Left: $loader"
  check_out_contains "  Outside: $loader"
  check_out_contains "  Dep.Base: $read"
  check_out_contains "  Dep.Up: $read"
  check_out_contains "paperlean: no native library of bad: $generic"
  # (the library of what it depends on stays as it was, so that this still holds)
  check_out_contains "paperlean: no native library of needy: not built (bad has no native library)"
  lacks "no .c"
  lacks "$builtin"
  lacks "  Dep.Left: $missing"
  lacks "  Outside: $outside"
  lacks "$unsupported"
  capture lake paperlean status
  unchanged_status
  check_out_contains "Dep.Gone $runs $outdated"
  check_out_contains "Dep.Left $runs $outdated"
  check_out_contains "Dep.Base $runs $outdated"
  check_out_contains "Dep.Up $runs $outdated"
  check_out_contains "Outside $runs $outdated"
  check_out_contains "Pre $runs $outdated"
  check_out_contains "native library of bad: $generic"
  lacks "no .c"
  lacks "$builtin"
  lacks "Dep.Left $runs $missing"
  lacks "Dep.Up $runs it imports one that does"
  lacks "$unsupported"
}
first_state no-c
capture lake paperlean status
check_out_contains "Dep.Gone $runs no .c"
second_state
capture lake paperlean prepare other
told_of_the_files
# ... and so it stays, as what the next pack is compared with is this one
capture lake paperlean prepare other
told_of_the_files
capture lake paperlean clean other
told_of_the_files

first_state no-c
second_state
capture lake paperlean clean other
told_of_the_files

# What changed still runs in the interpreter, so that a `prepare` counts what imports it, the next
# one too, for which it is only `outdated`.
first_state no-c
second_state
capture lake paperlean prepare other
capture lake paperlean prepare user
check_out_contains "user: 1 modules, 1 interpreted unless a plugin loads them"
capture lake paperlean prepare user
check_out_contains "user: 1 modules, 1 interpreted unless a plugin loads them"

# A `prepare` of the package finds out anew.
capture lake paperlean prepare dep
compile
check_out_contains "  Dep.Left: $missing"
check_out_contains "  Outside: $outside"
lacks "  Dep.Gone"
lacks "  Dep.Base"
capture lake paperlean status
lacks "Dep.Left $runs $outdated"
lacks "Outside $runs $outdated"
check_out_contains "Dep.Left $runs $missing"
# (of the package alone: the others stay as they were)
check_out_contains "Pre $runs $outdated"

# A module that did not change still imports one that runs in the interpreter, though that one changed:
# its library is kept, as are those it is linked against, so that nothing gives that one native code.
first_state
# (`base`, which `Dep.Up` uses, stays as it was, so that Lake builds `Dep.Up` to the same files)
printf 'builtin_initialize baseRef : IO.Ref Nat ← IO.mkRef 1\ndef base : Nat := 1\ndef baseToo : Nat := 1\n' > dep/Dep/Base.lean
run lake build Root
capture lake paperlean prepare other
compile
unchanged_build
check_out_contains "  Dep.Base: $read"
check_out_contains "that import one that does"
capture lake paperlean status
unchanged_status
check_out_contains "Dep.Base $runs $outdated"
check_out_contains "Dep.Up $runs it imports one that does"

# Without the pack (here deleted from the cache, which `prepare` then packs again), the files cannot be
# compared. Nothing that was found is said, and what the loader says is true whether they changed or not.
first_state
rm -rf "$PAPERLEAN_CACHE_DIR"/prepared/*/pack/dep-*
capture lake paperlean prepare other
compile
check_out_contains "  Dep.Left: $loader"
check_out_contains "  Dep.Base: its library does not use it"
lacks "$missing"
lacks "$builtin"
capture lake paperlean status
check_out_contains "Dep.Left $runs $outdated"
check_out_contains "Dep.Up $runs $outdated"
# (why `bad` has no library is not a matter of the pack)
check_out_contains "native library of bad: not built ($unsupported"

# Why a package has no library is checked where it is said, and where it is kept.
failure_stays() {
  compile
  check_out_contains "paperlean: no native library of bad: not built ($unsupported"
  capture lake paperlean status
  check_out_contains "native library of bad: not built ($unsupported"
  lacks "$generic"
}
failure_gone() {
  compile
  check_out_contains "paperlean: no native library of bad: $generic"
  lacks "$unsupported"
  capture lake paperlean status
  check_out_contains "native library of bad: $generic"
  lacks "$unsupported"
}
kept_gone() {
  ! grep -Fq "$unsupported" .lake/paperlean/env.json || fail "the reason was kept, of other inputs"
}

# The source is repaired and built, and nothing is prepared. `status` checks what it says of a module too.
first_state
printf 'def shadow : Nat := 2\n' > bad/Collides.lean
printf 'def left (n : Nat) : Nat := n\n' > dep/Dep/Left.lean
run lake build Root UsePre FarAside Plug
failure_gone
check_out_contains "Dep.Left $runs $outdated"
lacks "Dep.Left $runs $missing"
check_out_contains "Dep.Stays $runs $missing"
capture lake paperlean prepare bad
check_out_contains "bad: 2 modules"
lacks "not built (bad"
lacks "bad: not built"

# The rejected module is deleted, with its library, and only the other package is prepared.
first_state
rm bad/Collides.lean
printf 'name = "bad"\ndefaultTargets = ["Bad"]\n[[lean_lib]]\nname = "Bad"\n' > bad/lakefile.toml
root_imports ""
run lake build Root UsePre FarAside Plug
failure_gone
capture lake paperlean prepare other
kept_gone
failure_gone
capture lake paperlean prepare bad
check_out_contains "bad: 1 modules"
lacks "bad: not built"

# Its source alone is deleted: Lake keeps the compiled files, and the library stays in the lakefile. With
# it go a module and a module outside the default libraries, of which `status` no longer says anything.
first_state
rm bad/Collides.lean ../far/FarAside.lean dep/Dep/Left.lean
printf 'import Dep.Up\nimport Dep.Gone\nimport Dep.Stays\n' > dep/Dep.lean
root_imports ""
run lake build Root UsePre Plug
failure_gone
lacks "Dep.Left "
lacks "FarAside "
check_out_contains "Dep.Stays $runs $missing"

# Only the default targets change: no file does.
first_state
printf 'name = "bad"\ndefaultTargets = ["Bad"]\n[[lean_lib]]\nname = "Bad"\n[[lean_lib]]\nname = "Collides"\n' > bad/lakefile.toml
failure_gone
capture lake paperlean prepare other
kept_gone
failure_gone
capture lake paperlean prepare bad
check_out_contains "bad: 1 modules"
lacks "bad: not built"

# Without its `.c`, a module is no longer tried. (No build: that would rebuild the module.) And of a
# package that has left the workspace, nothing can be compared.
first_state
cp lakefile.toml lakefile.full
cat > lakefile.toml <<'END'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "dep"
path = "dep"
[[require]]
name = "other"
path = "other"
[[lean_lib]]
name = "Root"
END
capture lake paperlean status
check_out_contains "native library of bad: $generic"
lacks "$unsupported"
cp lakefile.full lakefile.toml
capture lake paperlean status
check_out_contains "native library of bad: not built ($unsupported"
bad_lakefile 'weakLinkArgs = ["-lm"]
'
capture lake paperlean status
check_out_contains "native library of bad: $generic"
bad_lakefile
capture lake paperlean status
check_out_contains "native library of bad: not built ($unsupported"
rm bad/.lake/build/ir/Collides.c
capture lake paperlean status
check_out_contains "native library of bad: $generic"

# What the attempt did not depend on leaves the reason, like a comment in the lakefile or a module that it
# did not try, as its library is not a default one; other link arguments, or another dependency, do not.
first_state
printf '# a comment\n' >> bad/lakefile.toml
failure_stays
run lake build BadAside
failure_stays
capture lake paperlean prepare other
failure_stays
bad_lakefile 'moreLinkArgs = ["-lm"]
'
failure_gone
needy_lakefile
compile
check_out_contains "paperlean: no native library of needy: $generic"
lacks "bad has no native library"

# What a library is compiled with is an input like what it links with: without `moreLeancArgs` it links, as
# `prepare` of the package shows, and none of its files changed. Nothing says so before it is tried again,
# so that the reason of the linker must not be said, also after a partial run.
linker_stays() {
  compile
  check_out_contains "paperlean: no native library of nopic: $linker"
  capture lake paperlean status
  check_out_contains "native library of nopic: $linker"
}
linker_gone() {
  capture lake paperlean status
  check_out_contains "native library of nopic: $generic"
  lacks "external command"
  compile
  check_out_contains "paperlean: no native library of nopic: $generic"
  lacks "external command"
}
if [ "$(uname)" = Linux ]; then
  first_state
  linker_stays
  capture lake paperlean prepare other
  linker_stays
  lib_lakefile nopic Nopic 'moreLinkArgs = ["-Wl,-z,text"]
'
  linker_gone
  capture lake paperlean prepare other
  ! grep -Fq "external command" .lake/paperlean/env.json || fail "the reason was kept, of other inputs"
  linker_gone
  capture lake paperlean prepare nopic
  check_out_contains "nopic: 1 modules"
  lacks "nopic: not built"
  # ... and with the weak ones
  nopic_args='weakLeancArgs = ["-fno-PIC"]
moreLinkArgs = ["-Wl,-z,text"]
'
  first_state
  capture lake paperlean status
  check_out_contains "native library of nopic: $linker"
  lib_lakefile nopic Nopic 'moreLinkArgs = ["-Wl,-z,text"]
'
  linker_gone
  nopic_args='moreLeancArgs = ["-fno-PIC"]
moreLinkArgs = ["-Wl,-z,text"]
'
fi

# Likewise of a module that they kept from compiling, which is left out with a reason of its own: its
# files do not change either.
first_state
lib_lakefile flag Flag
capture lake paperlean status
check_out_contains "Flag $runs $outdated"
check_out_contains "native library of flag: 0 $changed"
lacks "compile failed"
compile
check_out_contains "  Flag: $loader"
lacks "compile failed"

# A library that is a default one now, and one that no longer loads as a plugin: no file changed, and the
# lakefile says otherwise than `prepare` found. That reaches what depends on that package, whose module
# imported what a plugin loaded, and it is said at once: a build would rebuild that module, and that
# would say so for the wrong reason. A package that depends on neither stays.
first_state
sed 's/defaultTargets = \["Far"\]/defaultTargets = ["Far", "FarOut", "FarAside"]/' ../far/lakefile.toml > ../far/lakefile.new
mv ../far/lakefile.new ../far/lakefile.toml
grep -v precompileModules pre/lakefile.toml > pre/lakefile.new
mv pre/lakefile.new pre/lakefile.toml
config_told() {
  capture lake paperlean status
  check_out_contains "FarOut $runs $outdated"
  check_out_contains "FarAside $runs $outdated"
  check_out_contains "Pre $runs $outdated"
  check_out_contains "Plug $runs $outdated"
  check_out_contains "native library of pre: 1 $changed"
  check_out_contains "native library of plug: 1 $changed"
  check_out_contains "Dep.Stays $runs $missing"
  lacks "FarOut $runs $outside"
  lacks "FarAside is in no default library"
  lacks "Pre loads as a plugin"
  lacks "whose code a plugin loads"
  lacks "$unless_plugin"
  lacks "1 interpreted unless a plugin loads them"
}
config_told
capture lake paperlean prepare other
! grep -Fq -e "whose code a plugin loads" -e "$unless_plugin" .lake/paperlean/env.json ||
  fail "what was found was kept, of another configuration"
config_told
compile
check_out_contains "  FarOut: $loader"
lacks "  FarOut: $outside"
