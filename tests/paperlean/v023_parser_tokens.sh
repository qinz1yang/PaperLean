# Compare the registered parser fold with the original scoped fold. The real module supplies
# scoped syntax. Synthetic rows exercise both sides of the verified density gate and malformed entries.
cd "$TMP_DIR"
cp "$TEST_DIR/paperlean/parser_tokens/"*.lean .
run lean -o TokenScope.olean TokenScope.lean
run lean -c Probe.c Probe.lean
run leanc ${LEANC_OPTS-} -O2 -o probe Probe.c
run ./probe make "$TMP_DIR/parts" "$TMP_DIR/parser.paperlean"
export LEAN_PATH="$TMP_DIR/parts:$TMP_DIR"
export LEAN_OLEAN_PACK="$TMP_DIR/parser.paperlean"
cat > Frontend.lean <<'END'
prelude
import Dense
import TokenScope
open scoped ParserTokenScope
example : Nat := 0
END
for mode in default legacy check; do
  capture env PAPERLEAN_IMPORT="$mode" PAPERLEAN_IMPORT_TIMING=1 lean Frontend.lean
  if [ "$mode" != legacy ]; then
    check_out_contains "paperlean-counter parser.deduplicateGlobalTokens"
  else
    ! grep -q 'paperlean-counter parser.deduplicateGlobalTokens' "$CAPTURED.out.produced" ||
      fail "parser token optimization used in $mode mode"
  fi
  capture env PAPERLEAN_IMPORT="$mode" PAPERLEAN_IMPORT_TIMING=1 ./probe "$(lean --print-prefix)"
  check_out_contains "parser token folds agree"
  for fixture in real sparse small dense empty badCategory badConstant; do
    count=$(awk -v fixture="$fixture" '
      $0 == "parser-probe begin " fixture { active=1 }
      $0 == "parser-probe end " fixture { active=0 }
      active && $0 == "paperlean-counter parser.deduplicateGlobalTokens" { n++ }
      END { print n+0 }
    ' "$CAPTURED.out.produced")
    expect=0
    case "$mode/$fixture" in
      default/real|default/dense|default/empty|default/badCategory|default/badConstant|\
      check/real|check/dense|check/empty|check/badCategory|check/badConstant) expect=1 ;;
    esac
    [ "$count" = "$expect" ] || fail "parser token gate: $mode/$fixture expected $expect, got $count"
  done
done
# The checker must detect an altered skipped transition in the registered parser.
capture_exit 1 env PAPERLEAN_IMPORT=check ./probe "$(lean --print-prefix)" fault
check_out_contains "imported state of Lean.Parser.parserExtension differs from the fold"
