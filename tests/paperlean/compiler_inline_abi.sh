# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# `ToLCNF.toLCNF` and `Elab.addNonRecAux` are upstream bodies.  If either is
# compiled into an importer's code it must not reach a declaration that only
# PaperLean has, or official Lean cannot link the result.  The project's ABI
# audit follows every body an importer may inline or specialize; this test
# rejects the two assigned paths (and prints the rest of the class).

WS="$TMP_DIR/compiler-inline-abi"
mkdir -p "$WS"
cp "$TEST_DIR/paperlean/inline_abi.lean" "$WS/"
cd "$WS"
capture lean inline_abi.lean
if grep -qE '^Lean\.PaperLean\.(markOriginalHeads|ProofConversion\.optimize):' \
    "$CAPTURED.out.produced"; then
  grep -E '^Lean\.PaperLean\.(markOriginalHeads|ProofConversion\.optimize):' \
    "$CAPTURED.out.produced" >&2
  fail "an upstream body reaches PaperLean-only code"
fi
# Do not hide the remaining class; it is tracked separately.
grep ': a declaration of ' "$CAPTURED.out.produced" >&2 || true
true
