# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
"""The configured cache root may be a link. Its managed children must stay within it."""
import json
import os
from pathlib import Path
import subprocess
import sys

exe = Path(sys.argv[1]).resolve()
home = Path(sys.argv[2]).resolve()
home.mkdir()


def run(op, directory, value="0", ok=True):
    proc = subprocess.run([str(exe), op, str(directory), str(value)], timeout=5,
                          capture_output=True, text=True)
    assert (proc.returncode == 0) == ok, (op, directory, proc.returncode, proc.stderr)
    return proc.stdout.strip()


def build(root):
    return Path(run("dir", root))


def partition(name):
    root = home / name
    directory = build(root / "cache")
    directory.mkdir(parents=True)
    outside = root / "outside"
    outside.mkdir()
    return directory, outside


def sentinel(path):
    path.write_text("external")
    os.utime(path, (1, 1))


# Ordinary collection still respects recent uses and removes stale objects and input files.
directory, _ = partition("ordinary")
for name in ("objects", "inputs", "pack", "native"):
    (directory / name).mkdir()
old = directory / "objects/old.o"
sentinel(old)
new = directory / "objects/new.o"
new.write_text("recent")
entry = directory / "inputs/warm.paperlean"
entry.write_text("current")
run("touch", directory, "inputs/warm.paperlean")
run("collect", directory, "3600")
assert entry.exists() and new.exists() and not old.exists()
run("collect", directory, "0")
assert not entry.exists() and new.exists()

# Creating symlinks can require elevated privileges on Windows.
if os.name == "posix":
    for kind in ("pack", "native", "inputs", "objects", "users", "used"):
        directory, outside = partition("dir-" + kind)
        name = "pack-entry" if kind == "used" else "sentinel"
        victim = outside / name
        sentinel(victim)
        (directory / kind).symlink_to(outside, target_is_directory=True)
        if kind == "used":
            (directory / "pack/entry").mkdir(parents=True)
        run("collect", directory)
        assert victim.read_text() == "external", kind
        if kind == "users":
            run("user", directory, home / "workspace", ok=False)
        if kind == "used":
            run("touch", directory, "pack/entry", ok=False)
        assert sorted(p.name for p in outside.iterdir()) == [name], kind

    for kind in ("symlink", "hardlink", "fifo"):
        directory, outside = partition("marker-" + kind)
        ss = outside / "sentinel"
        sentinel(ss)
        (directory / "used").mkdir()
        (directory / "users").mkdir()
        ws = home / "workspace"
        userfile = directory / "users" / (run("key", directory, ws) + ".json")
        marker = directory / "used/pack-entry"
        for path in (marker, userfile):
            if kind == "hardlink":
                os.link(ss, path)
            elif kind == "symlink":
                path.symlink_to(ss)
            else:
                os.mkfifo(path)
        run("touch", directory, "pack/entry")
        run("user", directory, ws)
        assert ss.read_text() == "external" and not marker.is_symlink()
        assert marker.read_bytes() == b"" and not userfile.is_symlink()
        assert json.loads(userfile.read_text()) == {"workspace": str(ws)}

    for kind in ("symlink", "fifo"):
        directory, outside = partition("registry-" + kind)
        entry = directory / "pack/live"
        entry.mkdir(parents=True)
        (directory / "users").mkdir()
        f = directory / "users/damaged"
        slots = directory / "slots.json"
        victim = outside / "external"
        sentinel(victim)
        for path in (f, slots):
            if kind == "fifo":
                os.mkfifo(path)
            else:
                path.symlink_to(victim)
        run("collect", directory)
        assert entry.exists() and victim.read_text() == "external"
        assert f.is_fifo() if kind == "fifo" else f.is_symlink()

    for component in ("prepared", "build"):
        root = home / ("parent-" + component)
        directory = build(root / "cache")
        outside = root / "outside"
        outside.mkdir(parents=True)
        alias = directory.parent if component == "prepared" else directory
        alias.parent.mkdir(parents=True)
        alias.symlink_to(outside, target_is_directory=True)
        inner = outside / directory.name if component == "prepared" else outside
        vulnerable = inner / "pack/sentinel"
        vulnerable.parent.mkdir(parents=True)
        sentinel(vulnerable)
        run("collect", directory)
        run("touch", directory, "pack/foreign", ok=False)
        assert vulnerable.read_text() == "external" and not (inner / "used").exists()

    # A configured root located through a symlink is still usable.
    target = home / "legitimate-target"
    target.mkdir()
    alias = home / "configured-root"
    alias.symlink_to(target, target_is_directory=True)
    directory = build(alias)
    run("touch", directory, "inputs/root")
    assert (build(target) / "used/inputs-root").is_file()
    (directory / "inputs").mkdir()
    (directory / "inputs/root").write_text("current")
    run("collect", directory, "3600")
    assert (directory / "inputs/root").exists()
    run("collect", directory)
    assert not (directory / "inputs/root").exists()

print("cache containment and ordinary cleanup passed")
