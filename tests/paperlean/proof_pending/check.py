# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
from pathlib import Path
import subprocess
import sys

root = Path(sys.argv[1])
for jobs in (1, 4):
    command = ["lean", f"-j{jobs}", "-o", f"Pending{jobs}.olean", "Pending.lean"]
    result = subprocess.run(command, cwd=root, text=True, capture_output=True, timeout=30, check=True)
    expected = [
        "pending predecessor held",
        "theorem body visible before release: certificate",
        "predecessor and dependent frontend declaration checked",
        "eligible ready theorem uses certificate",
        "'pendingVia' does not depend on any axioms",
        "'readyVia' does not depend on any axioms",
    ]
    assert result.stdout.splitlines() == expected, (command, result.stdout, result.stderr)

if (root / "Pending1.olean").read_bytes() != (root / "Pending4.olean").read_bytes():
    raise RuntimeError("the pending predecessor changed the emitted .olean across job counts")

# The simulated predecessor publishes its body only after optimize returns. A blocking
# lookup will time out here; this is independent of scheduling or host speed.
for jobs in (1, 4):
    subprocess.run(["lean", f"-j{jobs}", "PendingBinder.lean"], cwd=root, timeout=30, check=True)
