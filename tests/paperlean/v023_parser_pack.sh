# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
case "$(uname -s)" in Darwin|Linux) ;; *) exit 0 ;; esac
cd "$TMP_DIR"
cp "$TEST_DIR/paperlean/v023_parser_pack.lean" Hint.lean
run lean -c hint.c Hint.lean
run leanc hint.c -o hint
run ./hint make "$TMP_DIR/parts"
run python3 "$TEST_DIR/paperlean/v023_parser_pack_fault.py" "$TMP_DIR/parts"
capture ./hint pack "$TMP_DIR/parts" "$TMP_DIR/parser.paperlean"
check_out_contains "packed 6"
capture env LEAN_PATH="$TMP_DIR/parts" LEAN_OLEAN_PACK="$TMP_DIR/parser.paperlean" \
  PAPERLEAN_IMPORT_TIMING=1 ./hint new "$TMP_DIR/parts"
check_out_contains "new [2, 1, 0, 0, 0, 0, 0, 0, 0, 0]"
check_out_contains "paperlean-counter parser.prepareHint=dense"
check_out_contains "paperlean-counter parser.prepareHint=sparse"
# A bad token size disqualifies the hint. Never inspect it before the earlier parser error.
printf 'prelude\nimport Malformed\n' > Use.lean
for mode in default legacy check; do
  capture_exit 1 env LEAN_PATH="$TMP_DIR/parts" LEAN_OLEAN_PACK="$TMP_DIR/parser.paperlean" \
    PAPERLEAN_IMPORT="$mode" lean Use.lean
  check_out_contains 'Unknown constant `MissingParser`'
done
# A dense hint can enable the fold for subsequent unpacked rows or for an
# unsampled position of the hinted row itself. Both must reach the stock error.
printf 'prelude\nimport Dense\nimport LooseBad\n' > Cross.lean
printf 'prelude\nimport Wrapped\n' > Same.lean
for source in Cross.lean Same.lean; do
  for mode in default legacy check; do
    capture_exit 1 env LEAN_PATH="$TMP_DIR/parts:$TMP_DIR/loose" LEAN_OLEAN_PACK="$TMP_DIR/parser.paperlean" \
      PAPERLEAN_IMPORT="$mode" PAPERLEAN_IMPORT_TIMING=1 lean "$source"
    check_out_contains 'Unknown constant `MissingParser`'
    if [ "$mode" != legacy ]; then
      check_out_contains "paperlean-counter parser.deduplicateGlobalTokens"
    fi
  done
done
