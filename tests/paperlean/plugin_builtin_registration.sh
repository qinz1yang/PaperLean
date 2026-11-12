# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# A plugin that a setup file loads can register a builtin attribute entry after `parseHeader` has
# built the dummy environment (and so after the builtin table was first materialized).  The
# import's environment must see it; a state cached from the first `mkInitial` without noticing the
# later registration would silently drop the entry.
DIR="$TMP_DIR/plugin-builtin"
mkdir -p "$DIR"
cat > "$DIR/Plugin.lean" <<'EOF'
import Lean

open Lean Elab

def pluginMacro : Macro := fun _ => `(42)

builtin_initialize
  Lean.Elab.macroAttribute.addBuiltin `my_builtin_macro `pluginMacro pluginMacro
EOF
cat > "$DIR/Use.lean" <<'EOF'
import Lean

syntax (name := my_builtin_macro) "my_builtin_macro" : term

#eval my_builtin_macro
EOF
cat > "$DIR/setup.json" <<EOF
{"name":"Use","package":null,"isModule":false,"dynlibs":[],"importArts":{},"options":{},"plugins":[{"path":"$DIR/Plugin.so","initFn":"initialize_Plugin"}]}
EOF
# The public structure keeps upstream's three fields, in upstream's order: official code compiled
# against Lean reads `tableRef` and `ext` by their layout.
cat > "$DIR/Layout.lean" <<'EOF'
import Lean

open Lean

def layout (attr : KeyedDeclsAttribute Nat) :
    KeyedDeclsAttribute.Def Nat × IO.Ref (KeyedDeclsAttribute.Table Nat) ×
      KeyedDeclsAttribute.Extension Nat :=
  (attr.defn, attr.tableRef, attr.ext)
EOF
cd "$DIR"
run lean -c Plugin.c Plugin.lean
run leanc -shared -DLEAN_EXPORTING -o Plugin.so Plugin.c
run lean -c Layout.c Layout.lean
capture lean --setup setup.json Use.lean
check_out_contains "42"
