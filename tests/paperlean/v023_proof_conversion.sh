# The same source proof on ordinary, bounded, dependent, and unsupported inputs.
cp "$TEST_DIR/paperlean/proof_conversion/"*.lean "$TMP_DIR/"
cd "$TMP_DIR"
export LEAN_PATH="$TMP_DIR"
run lean -o ProofBase.olean ProofBase.lean
run lean -j1 -o ProofCases.olean ProofCases.lean
cp ProofCases.olean.private first.private
run lean -j4 -o ProofCases.olean ProofCases.lean
run cmp first.private ProofCases.olean.private
