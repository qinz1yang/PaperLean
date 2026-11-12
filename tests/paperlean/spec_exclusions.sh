# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Specializations that Lean's own modules have only as PaperLean builds them (made in the upstream
# modules whose source PaperLean changes, `Lean.PaperLean.SpecExclusions`) must not be reused by code
# PaperLean compiles in other modules: official Lean, reading that code, could neither link nor
# interpret calls to them. The callers of `inline_abi.sh` (`Callers.lean`) reused one on 0.2.3:
# `addMessageContextFull` specialized in `Lean.LibrarySuggestions.SymbolFrequency`, which official
# rc3's library does not define (`rev-compiler` compiler-2).

cd "$TMP_DIR"
# the callers of inline_abi.sh
sed -n "/^cat > \"\$TMP_DIR\/Callers.lean\" <<'EOF2'\$/,/^EOF2\$/p" "$TEST_DIR/paperlean/inline_abi.sh" | sed '1d;$d' > Callers.lean
[ -s Callers.lean ] || fail "could not extract Callers.lean from inline_abi.sh"
run lean -c Callers.c Callers.lean
[ -s Callers.c ] || fail "no C file"
# a specialization of a private declaration of one of the modules PaperLean changes, referenced from
# Callers.c without being defined there
modules='Init_System_IO|Lake_Build_Actions|Lake_Build_Index|Lake_Build_Run|Lean_Compiler_LCNF_EmitC|Lean_Compiler_LCNF_ToLCNF|Lean_Elab_InfoTree_Basic|Lean_Elab_Parallel|Lean_Elab_PreDefinition_Eqns|Lean_Elab_PreDefinition_Structural_Eqns|Lean_LibrarySuggestions_Basic|Lean_LibrarySuggestions_SineQuaNon|Lean_LibrarySuggestions_SymbolFrequency|Lean_Meta_Eqns|Lean_Meta_FunInfo|Lean_Meta_Tactic_LibrarySearch|Lean_Meta_Tactic_Simp_Rewrite|Lean_Meta_WHNF|Lean_Parser_Extension|Std_Async_Select|Std_Sync_Broadcast|Std_Sync_CancellationContext|Std_Sync_Channel'
grep -oE "l_[A-Za-z0-9_]*_at___[A-Za-z0-9_]*__private_($modules)_0__[A-Za-z0-9_]*_spec__[0-9]+" Callers.c | sort -u > reused.txt || true
if [ -s reused.txt ]; then
  cat reused.txt
  fail "Callers.c calls specializations that only PaperLean's build of Lean's modules has"
fi
true
