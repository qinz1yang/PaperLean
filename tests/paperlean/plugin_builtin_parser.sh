# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# A setup plugin can register a builtin parser (and so a new token) after `parseHeader` has built
# the dummy environment.  The import's environment must see the token; a token table cached from
# the first `mkInitial` without noticing the later registration would silently lack it.  The global
# `builtinTokenTable` must stay a public `IO.Ref TokenTable`.  Registration must also still reject
# an empty token at the time of registration, so that a plugin that catches the error sees it there
# and not when a later environment is created.
DIR="$TMP_DIR/plugin-parser"
mkdir -p "$DIR"
cat > "$DIR/Plugin.lean" <<'EOF'
import Lean

open Lean Parser

def pluginParser : Parser := leading_parser "my_builtin_token"

builtin_initialize
  Lean.Parser.addBuiltinLeadingParser `term `pluginParser pluginParser 0
EOF
cat > "$DIR/Use.lean" <<'EOF'
import Lean

open Lean Parser in
#eval show CoreM Unit from do
  let env ← getEnv
  if (getTokenTable env).find? "my_builtin_token" |>.isSome then
    IO.println "token present"
  else
    IO.println "token absent"
#check (Lean.Parser.builtinTokenTable : IO.Ref Lean.Parser.TokenTable)
EOF
cat > "$DIR/setup.json" <<EOF
{"name":"Use","package":null,"isModule":false,"dynlibs":[],"importArts":{},"options":{},"plugins":[{"path":"$DIR/Plugin.so","initFn":"initialize_Plugin"}]}
EOF
cd "$DIR"
run lean -c Plugin.c Plugin.lean
run leanc -shared -DLEAN_EXPORTING -o Plugin.so Plugin.c
capture lean --setup setup.json Use.lean
check_out_contains "token present"

# A registration that collects an empty token must fail during the plugin's registration, with the
# old message, and the plugin must be able to catch it: a check deferred to the next `mkInitial`
# would print `BAD-ACCEPTED` here (and fail later, outside the plugin's `try`).
cat > "$DIR/BadPlugin.lean" <<'EOF'
import Lean

open Lean Parser

def badParser : Parser := {
  info := { collectTokens := fun _ => [""], collectKinds := id, firstTokens := .epsilon }
  fn := fun _ s => s }

builtin_initialize
  try
    Lean.Parser.addBuiltinLeadingParser `term `badParser badParser 0
    IO.println "BAD-ACCEPTED"
  catch e =>
    IO.println s!"BAD-CAUGHT {e}"
EOF
cat > "$DIR/Bad.lean" <<'EOF'
import Lean
EOF
cat > "$DIR/setup-bad.json" <<EOF
{"name":"Bad","package":null,"isModule":false,"dynlibs":[],"importArts":{},"options":{},"plugins":[{"path":"$DIR/BadPlugin.so","initFn":"initialize_BadPlugin"}]}
EOF
run lean -c BadPlugin.c BadPlugin.lean
run leanc -shared -DLEAN_EXPORTING -o BadPlugin.so BadPlugin.c
capture lean --setup setup-bad.json Bad.lean
check_out_contains "BAD-CAUGHT"
check_out_contains "invalid empty symbol"
if grep -Fq "BAD-ACCEPTED" "$CAPTURED.out.produced"; then
  fail "the empty token was not rejected during registration"
fi
