# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Deterministic publication ordering test; called by prepare_slots.sh."""

import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys
import time

DRIVER = Path(sys.argv[1]).resolve()
ROOT = Path(sys.argv[2]).resolve() / "slots"
ROOT.mkdir()
children = []
logs = []
ALIGN = 0x40000000
START = 0x400000000000


def wait_until(test, description):
    limit = time.monotonic() + 60
    while time.monotonic() < limit:
        if test():
            return
        for child in children:
            if child.poll() not in (None, 0):
                raise AssertionError(f"writer exited {child.returncode} while {description}")
        time.sleep(0.01)
    raise AssertionError(f"timed out {description}")


def spawn(args, log_name):
    log = open(ROOT / f"{log_name}.log", "wb")
    logs.append(log)
    child = subprocess.Popen(["lean", "--run", str(DRIVER), *map(str, args)], stdout=log,
                             stderr=subprocess.STDOUT)
    children.append(child)
    return child


def finish(child):
    assert child.wait(timeout=60) == 0, f"writer exited {child.returncode}"


def gate(name):
    path = ROOT / name
    path.mkdir()
    return path


def slots(cache):
    return json.loads((cache / "slots.json").read_text())


def opened_lock(pid, path):
    # The parent holds the lock, so the writer keeps its descriptor open while
    # blocked inside the production allocator/publisher. No scheduling delay
    # or assumption about the kernel's eventual waiter order is needed.
    fds = Path("/proc") / str(pid) / "fd"
    if fds.is_dir():
        for fd in fds.iterdir():
            try:
                if fd.samefile(path):
                    return True
            except OSError:
                continue
        return False
    # macOS has no procfs. lsof can inspect the test's own child.
    return subprocess.run(["lsof", "-nP", "-a", "-p", str(pid), "--", str(path)],
                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                          timeout=5).returncode == 0


def assert_disjoint(rows):
    rows = sorted(rows, key=lambda row: row["base"])
    for a, b in zip(rows, rows[1:]):
        assert a["base"] + a["size"] <= b["base"], (a, b)


try:
    cache = ROOT / "concurrent"
    a, b = gate("gate-a"), gate("gate-b")
    pa = spawn(["writer", cache, "a", a], "a")
    wait_until(lambda: (a / "ready").exists(), "waiting for first reservation")
    _, pending, base = (a / "ready").read_text().splitlines()
    before = (cache / "slots.json").read_bytes()
    lock_path = cache / "slots.lock"
    with lock_path.open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        (a / "release").touch()
        wait_until(lambda: opened_lock(pa.pid, lock_path), "publisher reaching slots.lock")
        assert (cache / pending).is_dir(), "publisher renamed its pack before taking slots.lock"
        assert not (cache / "pack/a").exists()
        (b / "release").touch()
        pb = spawn(["writer", cache, "b", b], "b")
        wait_until(lambda: (b / "started").exists(), "starting different-entry allocator")
        wait_until(lambda: opened_lock(pb.pid, lock_path), "allocator reaching slots.lock")
        assert not (b / "ready").exists(), "allocator bypassed the slot lock"
        assert (cache / "slots.json").read_bytes() == before, "metadata changed without the slot lock"
    # Either waiter may acquire the released lock first. The ranges must be
    # disjoint both before and after the pending owner's directory is renamed.
    finish(pa)
    finish(pb)
    rows = slots(cache)
    assert {r["entry"] for r in rows} == {"pack/a", "pack/b"}, rows
    assert all(r["size"] == ALIGN for r in rows), rows
    assert_disjoint(rows)
    assert next(r for r in rows if r["entry"] == "pack/a")["base"] == int(base)
    assert (cache / "pack/a/pack.paperlean").read_text() == "a"
    assert (cache / "pack/b/pack.paperlean").read_text() == "b"

    # A real rename failure happens after the metadata handoff (the target's parent is absent).
    # The original pending owner must be restored before the slots lock is released.
    failed = ROOT / "failed"
    finish(spawn(["rename-fails", failed], "failed"))
    pending = (failed / "pending").read_text()
    assert [r["entry"] for r in slots(failed)] == [pending]
    missing = ROOT / "missing"
    finish(spawn(["missing-slot", missing], "missing"))
    assert not (missing / "slots.json").exists(), "missing reservation was silently published"

    # Exercise the exact persisted states on each side of the atomic directory rename. These are
    # state fixtures, not claims that SIGKILL was injected between the helper's internal operations.
    # Before rename: final owner is recorded but absent, so reuse is safe. After rename: final owner
    # exists and must stay reserved even though its publisher has exited.
    for published in (False, True):
        crash = ROOT / f"crash-{published}"
        (crash / "pack").mkdir(parents=True)
        old = {"base": START, "size": ALIGN, "entry": "pack/previous"}
        if published:
            (crash / old["entry"]).mkdir()
        (crash / "slots.json").write_text(json.dumps([old]))
        g = gate(f"gate-crash-{published}")
        (g / "release").touch()
        finish(spawn(["writer", crash, "next", g], f"crash-{published}"))
        rows = slots(crash)
        current = next(r for r in rows if r["entry"] == "pack/next")
        assert current["base"] == START + (ALIGN if published else 0), rows
        assert_disjoint(rows)
    print("pack slot publication: different-key ordering, rollback and crash states passed")
finally:
    for child in children:
        if child.poll() is None:
            child.kill()
            child.wait()
    for log in logs:
        log.close()
    for path in ROOT.glob("*.log"):
        if path.stat().st_size:
            print(f"{path.name}:\n{path.read_text()}", file=sys.stderr)
