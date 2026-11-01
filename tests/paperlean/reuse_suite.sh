# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that Lean's own test files, the broadest normal code in the tree, give with reuse and the
# oracle on what they give with nothing reused: exit code, messages, `.olean`, `.ilean` and `.c`
# (`reuse_suite.py`). The rest of the suite runs with reuse off, as `lean` does unless a `paperlean`
# command asks for it; `PAPERLEAN_REUSE=1 PAPERLEAN_REUSE_ORACLE=1 ctest` runs all of it with reuse on.
python3 "$(dirname "$FILE")/reuse_suite.py" || fail "a file differs with reuse, the oracle found a difference, or a signal ended a run"
