# Official Lean must be able to use the candidate's public proof artifacts alone.
OFFICIAL=${OFFICIAL_LEAN_TOOLCHAIN:-$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3}
[ -x "$OFFICIAL/bin/lean" ] || fail "official Lean rc3 not found: $OFFICIAL"
mkdir -p "$TMP_DIR/producer/ProofCache" "$TMP_DIR/reader/ProofCache"
cd "$TMP_DIR/producer"
cat > lakefile.toml <<'TOML'
name = "proof-cache"
defaultTargets = ["ProofCache"]
[[lean_lib]]
name = "ProofCache"
TOML
cat > ProofCache/Base.lean <<'LEAN'
module
public structure Sample where
  value : Nat
  tag : Bool
@[expose] public def sample (n : Nat) : Sample := ⟨n, true⟩
public theorem sample_value (n : Nat) : (sample n).value = n := rfl
LEAN
cat > ProofCache.lean <<'LEAN'
module
public import ProofCache.Base
public theorem sample_succ (n : Nat) : (sample (n+1)).value = n+1 := sample_value _
LEAN
run lake paperlean build
[ -f .lake/build/ir/ProofCache.setup.paperlean ] || fail "did not exercise accelerated Lake setup"
cp .lake/build/lib/lean/ProofCache/Base.olean "$TMP_DIR/reader/ProofCache/"
cp .lake/build/lib/lean/ProofCache.olean "$TMP_DIR/reader/"
cd "$TMP_DIR/reader"
cat > Use.lean <<'LEAN'
module
public import ProofCache
public theorem fromPaperLean (n : Nat) : (sample (n+1)).value = n+1 := sample_succ n
#print axioms fromPaperLean
LEAN
# No candidate stdlib, source, IR, plugin, setup index, or prepared cache is on the reader's path.
# Without explicit importArts rc3 also requests its normal server companions by default.
# Use rc3's own setup schema to request just the public artifact for each module.
python3 - <<'PYSETUP'
import json
from pathlib import Path
r = Path.cwd()
for m in ["Use", "Bad"]:
    (r / (m + ".json")).write_text(json.dumps({
        "name": m, "isModule": True, "plugins": [], "dynlibs": [], "options": {},
        "importArts": {n: [[str(r / f)], []] for n, f in
                       [("ProofCache", "ProofCache.olean"), ("ProofCache.Base", "ProofCache/Base.olean")]}}))
PYSETUP
capture_exit 0 env -u LEAN_SYSROOT -u LEAN_OLEAN_PACK -u LEAN_IMPORT_IMAGE -u PAPERLEAN_CACHE_DIR \
  LEAN_PATH="$PWD" "$OFFICIAL/bin/lean" --setup=Use.json -o Use.olean Use.lean
check_out_contains "'fromPaperLean' does not depend on any axioms"
cat > Bad.lean <<'LEAN'
module
public import ProofCache
example : (sample 1).value = 2 := sample_value 1
LEAN
capture_exit 1 env -u LEAN_SYSROOT LEAN_PATH="$PWD" "$OFFICIAL/bin/lean" --setup=Bad.json Bad.lean
check_out_contains "Type mismatch"
mv ProofCache/Base.olean ProofCache/Base.saved
capture_exit 1 env -u LEAN_SYSROOT LEAN_PATH="$PWD" "$OFFICIAL/bin/lean" --setup=Use.json Use.lean
check_out_contains "ProofCache/Base.olean"

# Normal rc3 discovers prebuilt imports in the downstream project's standard library directory.
# Only the candidate dependency's three OLean parts cross into this fresh project.
normal="$TMP_DIR/normal"
lib="$normal/.lake/build/lib/lean"
donor="$TMP_DIR/producer/.lake/build/lib/lean"
mkdir -p "$lib/ProofCache"
cd "$normal"
cat > lakefile.toml <<'TOML'
name = "downstream"
defaultTargets = ["Downstream"]
[[lean_lib]]
name = "Downstream"
TOML
cat > Downstream.lean <<'LEAN'
module
public import ProofCache
public theorem downstream_sample (n : Nat) : (sample (n+1)).value = n+1 := sample_succ n
#print axioms downstream_sample
LEAN
stock=(env -u LEAN -u LEAN_SYSROOT -u LEAN_PATH -u LEAN_OLEAN_PACK -u LEAN_IMPORT_IMAGE
  -u PAPERLEAN_CACHE_DIR -u ELAN_TOOLCHAIN PATH="$OFFICIAL/bin:$PATH")
cli=("${stock[@]}" LEAN_PATH="$lib" "$OFFICIAL/bin/lean" Downstream.lean)
for part in olean olean.server olean.private; do
  for mod in ProofCache ProofCache/Base; do
    cp "$donor/$mod.$part" "$lib/$mod.$part"
  done
  case "$part" in
    olean) capture_exit 1 "${cli[@]}"; check_out_contains ".olean.server" ;;
    olean.server) capture_exit 1 "${cli[@]}"; check_out_contains ".olean.private" ;;
    olean.private) capture_exit 0 "${cli[@]}"; check_out_contains "'downstream_sample' does not depend on any axioms" ;;
  esac
done
[ ! -e "$lib/Downstream.olean" ] || fail "downstream build already has a consumer artifact"
run "${stock[@]}" "$OFFICIAL/bin/lake" build
[ -s "$lib/Downstream.olean" ] || fail "stock Lake did not build the downstream proof"
