# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# The public tables of builtin registrations read as official Lean's: `KeyedDeclsAttribute.tableRef`
# of builtin attributes and `Lean.Parser.builtinTokenTable`. The `lean` executable collects Lean's own
# builtin registrations while its library initializes and folds them into these tables before any
# other code runs (`Lean.PaperLean.flushBuiltinRegistrations`); afterwards every registration updates
# them as upstream does. Both direct reads (every key with its entries in order, every token) and
# direct writes interleaved with registrations at run time must give official Lean 4.35.0-rc3's
# output. It needs official Lean, at `$OFFICIAL_LEAN_TOOLCHAIN` or elan's, and fails without it.
OFFICIAL=${OFFICIAL_LEAN_TOOLCHAIN:-$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3}
[ -x "$OFFICIAL/bin/lean" ] ||
  fail "official Lean 4.35.0-rc3 is not at $OFFICIAL (set OFFICIAL_LEAN_TOOLCHAIN to where it is)"

cd "$TMP_DIR"
cat > Tables.lean <<'EOF'
import Lean
open Lean

/-- Every key of a builtin attribute's public table with its entries' names, in the table's order. -/
def dumpAttr {γ} (name : String) (attr : KeyedDeclsAttribute γ) : IO Unit := do
  let table ← attr.tableRef.get
  let rows := table.fold (init := (#[] : Array String))
    fun acc key (entries : List (KeyedDeclsAttribute.AttributeEntry γ)) =>
      acc.push s!"{name} {key}: {entries.map (·.toOLeanEntry.declName)} builtin={entries.all (·.isBuiltin)}"
  for row in rows.qsort (· < ·) do IO.println row
  IO.println s!"{name}: {rows.size} keys"

#eval dumpAttr "macro" Lean.Elab.macroAttribute
#eval dumpAttr "term" Lean.Elab.Term.termElabAttribute
#eval dumpAttr "command" Lean.Elab.Command.commandElabAttribute
#eval dumpAttr "tactic" Lean.Elab.Tactic.tacticElabAttribute
#eval dumpAttr "delab" Lean.PrettyPrinter.Delaborator.delabAttribute
#eval do
  let tokens ← Lean.Parser.builtinTokenTable.get
  let all := tokens.values.qsort (· < ·)
  for tk in all do IO.println s!"token {tk}"
  IO.println s!"tokens: {all.size}"

def m1 : Macro := fun _ => Macro.throwUnsupported
def m2 : Macro := fun _ => Macro.throwUnsupported
def m3 : Macro := fun _ => Macro.throwUnsupported

-- registrations at run time interleaved with direct writes to the public tables
#eval do
  let k := `paperlean_test_kind
  KeyedDeclsAttribute.addBuiltin Lean.Elab.macroAttribute k `m1 m1
  Lean.Elab.macroAttribute.tableRef.modify fun t =>
    t.insert k ({ key := k, declName := `m2, value := m2, isBuiltin := true } :: (t.find? k).getD [])
  KeyedDeclsAttribute.addBuiltin Lean.Elab.macroAttribute k `m3 m3
  let t ← Lean.Elab.macroAttribute.tableRef.get
  let entries : List (KeyedDeclsAttribute.AttributeEntry Macro) := (t.find? k).getD []
  let names := entries.map fun (e : KeyedDeclsAttribute.AttributeEntry Macro) => e.toOLeanEntry.declName
  IO.println s!"interleaved: {names}"
  Lean.Parser.builtinTokenTable.modify fun t => t.insert "paperlean_direct_tk" "paperlean_direct_tk"
  let t ← Lean.Parser.builtinTokenTable.get
  IO.println s!"direct token: {(t.find? "paperlean_direct_tk").isSome}, '(': {(t.find? "(").isSome}"
EOF
capture env -u LEAN_PATH "$OFFICIAL/bin/lean" Tables.lean
cp "$CAPTURED.out.produced" official.out
grep -q '^interleaved: \[m3, m2, m1\]$' official.out || fail "the probe does not test what it should: $(grep interleaved official.out)"
[ "$(grep -c '^token ' official.out)" -gt 100 ] || fail "the probe does not test what it should: few tokens"
grep -q '^macro: [1-9]' official.out || fail "the probe does not test what it should: no builtin macros"
capture lean Tables.lean
cp "$CAPTURED.out.produced" paperlean.out
$DIFF -- official.out paperlean.out || fail "PaperLean's public builtin tables differ from official Lean's"
