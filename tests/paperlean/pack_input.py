# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import sys

work = Path(sys.argv[1]).resolve() / "pack-input"
work.mkdir()
driver = Path(__file__).resolve().with_suffix(".lean")
lean = shutil.which("lean")


def run(args, env=None, limit=None, expected=0, prefix=()):
    def set_limit():
        hard = resource.getrlimit(resource.RLIMIT_NOFILE)[1]
        resource.setrlimit(resource.RLIMIT_NOFILE, (limit, hard))

    proc = subprocess.run([*prefix, lean, *map(str, args)], cwd=work,
                          env=os.environ | (env or {}), preexec_fn=set_limit if limit else None,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=90)
    text = proc.stdout.decode(errors="replace")
    assert proc.returncode == expected, (args, proc.returncode, text)
    return text


def identity(path):
    st = path.stat()
    return st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns


versions = []
for n, name in enumerate(("One", "Two")):
    (work / "R12.lean").write_text(f"def R12marker{name} : Nat := 0\n")
    output = work / f"version-{n}.olean"
    run(["-o", output, "R12.lean"])
    versions.append(output)

root = work / "root"
root.mkdir()
source = root / "R12.olean"
shutil.copyfile(versions[0], source)
alias = work / "alias"
alias.symlink_to(root, target_is_directory=True)
hard = work / "hard"
hard.mkdir()
os.link(source, hard / "R12.olean")  # Create before packing: linking changes ctime.
pack, hard_pack = work / "pack", work / "hard-pack"
run(["--run", driver, "pack", root, pack])
run(["--run", driver, "pack", hard, hard_pack])
(work / "Use.lean").write_text("import R12\n#check R12markerOne\n")
selections = [(root, pack, source), (alias, pack, source), (hard, hard_pack, hard / "R12.olean")]
for selected, chosen, _ in selections:
    env = {"LEAN_PATH": str(selected), "LEAN_OLEAN_PACK": str(chosen), "PAPERLEAN_IMPORT_TIMING": "1"}
    assert "modules.fast packed=1" in run(["Use.lean"], env=env)
assert "0/1 [R12.olean]" in run(["--run", driver, "index", root, pack])

# A pack is an independently readable cache copy. Its use requires the selected original's
# current identity, not permission to open that original again. Seatbelt can deny read-data
# without changing inode/ctime; the unpacked failure proves that this is a real denial.
# Each compiler process starts inside the sandbox, before it can admit/map the pack.
if sys.platform == "darwin" and Path("/usr/bin/sandbox-exec").exists():
    def sandbox(*denials):
        rules = "".join(f"(deny {kind} (literal {json.dumps(str(path))}))" for kind, path in denials)
        return ["/usr/bin/sandbox-exec", "-p", "(version 1)(allow default)" + rules]

    original = identity(source)
    for selected, chosen, denied_source in selections:
        deny_source = sandbox(("file-read-data", denied_source))
        deny_pack = sandbox(("file-read-data", chosen))
        deny_both = sandbox(("file-read-data", denied_source), ("file-read-data", chosen))
        for setting in ["fast", "legacy", "check"]:
            env = {"LEAN_PATH": str(selected), "LEAN_OLEAN_PACK": str(chosen),
                   "PAPERLEAN_IMPORT": setting, "PAPERLEAN_IMPORT_TIMING": "1"}
            out = run(["Use.lean"], env=env | {"LEAN_OLEAN_PACK": ""}, prefix=deny_source, expected=1)
            assert "failed to open file" in out, out
            out = run(["Use.lean"], env=env, prefix=deny_source)
            assert "R12markerOne : Nat" in out, out
            if setting == "fast":
                assert "modules.fast packed=1" in out, out
            # An unreadable pack cannot be admitted. The readable source still works.
            out = run(["Use.lean"], env=env, prefix=deny_pack)
            assert "R12markerOne : Nat" in out and "ignoring olean pack" in out, out
            assert "modules.fast packed=1" not in out, out
            out = run(["Use.lean"], env=env, prefix=deny_both, expected=1)
            assert "failed to open file" in out, out
        # freshFiles takes the root recorded by the pack, not its search-path alias.
        indexed_root = denied_source.parent
        out = run(["--run", driver, "index", indexed_root, chosen], prefix=deny_source)
        assert "0/1 [R12.olean]" in out, out
        # Metadata access is required: neither the importer nor the standalone inspector may
        # validate through a previously held directory or a different readable hardlink.
        deny_metadata = sandbox(("file-read-metadata", denied_source))
        out = run(["--run", driver, "index", indexed_root, chosen], prefix=deny_metadata)
        assert "1/1 []" in out, out
        env = {"LEAN_PATH": str(selected), "LEAN_OLEAN_PACK": str(chosen), "PAPERLEAN_IMPORT_TIMING": "1"}
        run(["Use.lean"], env=env | {"LEAN_OLEAN_PACK": ""}, prefix=deny_metadata, expected=1)
        out = run(["Use.lean"], env=env, prefix=deny_metadata, expected=1)
        assert "modules.fast packed=1" not in out, out
    assert identity(source) == original

# Restoring mtime/size after an in-place source change does not restore its recorded ctime.
# This must select the new declaration even though the old pack is still readable.
old = source.stat()
new_bytes = versions[1].read_bytes()
assert len(new_bytes) == old.st_size
source.write_bytes(new_bytes)
os.utime(source, ns=(old.st_atime_ns, old.st_mtime_ns))
now = source.stat()
assert (now.st_dev, now.st_ino, now.st_size, now.st_mtime_ns) == (old.st_dev, old.st_ino, old.st_size, old.st_mtime_ns)
assert now.st_ctime_ns != old.st_ctime_ns
(work / "Changed.lean").write_text("import R12\n#check R12markerTwo\n")
for selected, chosen, _ in selections:
    assert "1/1 []" in run(["--run", driver, "index", selected, chosen])
    env = {"LEAN_PATH": str(selected), "LEAN_OLEAN_PACK": str(chosen), "PAPERLEAN_IMPORT_TIMING": "1"}
    out = run(["Changed.lean"], env=env)
    assert "R12markerTwo : Nat" in out and "modules.fast packed=1" not in out, out
# Pack corruption and changed pack identity are covered in olean_pack.sh.

# First read must come from this pack. During subsequent imports, file and root replacement
# deliberately select a new file. The same unlinked roots must not exhaust a long-lived worker.
for mode, count, limit in [("file", 4, None), ("dir", 40, 32)]:
    current = work / f"live-{mode}"
    current.mkdir()
    shutil.copyfile(versions[0], current / "R12.olean")
    current_pack = work / f"pack-{mode}"
    run(["--run", driver, "pack", current, current_pack])
    env = {"LEAN_PATH": str(current), "LEAN_OLEAN_PACK": str(current_pack)}
    run(["--run", driver, "repeat", mode, current, *versions, str(count)], env=env, limit=limit)
