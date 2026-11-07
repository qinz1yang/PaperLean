# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
cd "$TMP_DIR"
cp "$TEST_DIR/paperlean/v023_proof_budget.lean" Budget.lean
run lean -c Budget.c Budget.lean
run ${CXX:-c++} -std=c++17 -I"$TEST_DIR/../src" -I"$(lean --print-prefix)/include" \
  -c "$TEST_DIR/paperlean/v023_proof_budget.cpp" -o probe.o
run leanc Budget.c probe.o -o budget
capture ./budget
check_out_contains "proof trial budgets ok"
