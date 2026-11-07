source_init "$1"
run_before "$1"
maybe_use_lean_header_snapshot "$1"

# `--root` to infer same private names as in the server
# Elab.inServer to allow for arbitrary `#eval`
capture_only "$1" \
  lean --root=.. -DprintMessageEndPos=true -Dlinter.all=false -DElab.inServer=true "${TEST_LEAN_ARGS[@]}" "$1"
normalize_mvar_suffixes
normalize_reference_urls
normalize_measurements
check_out_file
# A matching diagnostic followed by a signal is still a crashing test. Fixtures
# requiring a different ordinary failure code must state it explicitly.
EXPECTED_ELAB_EXIT=1
if [[ -f "$1.exit.expected" ]]; then
    EXPECTED_ELAB_EXIT=$(cat "$1.exit.expected")
    if [[ ! "$EXPECTED_ELAB_EXIT" =~ ^[1-9][0-9]{0,2}$ ]] || (( 10#$EXPECTED_ELAB_EXIT > 125 )); then
        echo "invalid expected elaborator exit in $1.exit.expected (expected 1..125)" >&2
        exit 1
    fi
fi
check_exit_is "$EXPECTED_ELAB_EXIT"

run_after "$1"
