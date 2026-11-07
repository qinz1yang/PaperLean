# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
cd "$TMP_DIR"
cp "$TEST_DIR/paperlean/proof_conversion/ProofBase.lean" .
cp "$TEST_DIR/paperlean/proof_pending/"{PendingTools,Pending,PendingBinder}.lean .
export LEAN_PATH="$TMP_DIR"
run lean -j1 -o ProofBase.olean ProofBase.lean
run lean -j1 -o PendingTools.olean PendingTools.lean
run python3 "$TEST_DIR/paperlean/proof_pending/check.py" "$TMP_DIR"
