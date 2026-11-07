# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
probe="$(pwd -P)/runtime_init.lean"
cd "$TMP_DIR"
cat > lakefile.toml <<'EOF'
name = "registrytest"
[[lean_lib]]
name = "Fixture"
EOF
printf 'module\npublic def fixture := 1\n' > Fixture.lean
export PAPERLEAN_CACHE_DIR="$PWD/user-cache"
export LAKE_ARTIFACT_CACHE=false
# Call the runtime APIs without loading libLake as a plugin. The registries,
# builtin-map hook and mutex operations must work in the interpreter itself.
capture env PAPERLEAN_ACCELERATE=1 lean --run "$probe"
check_out_contains "runtime registries initialized"
# Native Lake must admit exactly the same default facet providers.
run env PAPERLEAN_ACCELERATE=1 PAPERLEAN_SETUP_INDEX_KEEP=1 lake build +Fixture
grep -q '\[anonymous\]' .lake/build/ir/Fixture.setup.paperlean || fail "native Lake did not use indexed setup"
