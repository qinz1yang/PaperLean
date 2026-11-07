set -euo pipefail

# The producer receipt validates both snapshots and their imported artifacts before a warm hit.
python3 "$(dirname "${BASH_SOURCE[0]}")/build_lean_header_snapshots.py"
