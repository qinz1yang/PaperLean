# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
import json
import os
from pathlib import Path
import pwd
import shutil
import stat
import subprocess
import sys

work = Path(sys.argv[1]).resolve() / "private-cache"
work.mkdir(mode=0o755)
work.chmod(0o755)
lean = sys.argv[3] if len(sys.argv) > 3 else shutil.which("lean")
driver = [sys.argv[2]] if len(sys.argv) > 2 else [lean, "--run", str(Path(__file__).with_suffix(".lean"))]
secret = b"PAPERLEAN_PRIVATE_CACHE_TEST_503721"
source = work / "project"
source.mkdir(mode=0o700)
source.chmod(0o700)
lib = source / "lib"
lib.mkdir()
f = source / "Secret.lean"
f.write_text('module\n@[expose] public def privateText : String := "' + secret.decode() + '"\n')
subprocess.run([lean, "-o", str(lib / "Secret.olean"), str(f)], cwd=source, check=True, timeout=30)
results = []


def case(name):
    c = work / name
    c.mkdir(mode=0o755)
    c.chmod(0o755)
    return c, c / ".cache", c / ".cache/paperlean"


def run(c, mask=0o022, explicit=None, succeeds=True, canonical=False, deny_mode=False):
    env = os.environ.copy()
    env.pop("PAPERLEAN_CACHE_DIR", None)
    env["XDG_CACHE_HOME"] = str(c / ".cache")
    if explicit is not None:
        env["PAPERLEAN_CACHE_DIR"] = str(explicit)
    old = os.umask(mask)
    try:
        prefix = []
        if deny_mode:
            protected = explicit if explicit is not None else c / ".cache/paperlean"
            policy = '(version 1)(allow default)(deny file-write-mode (literal ' + json.dumps(str(protected)) + '))'
            prefix = ["/usr/bin/sandbox-exec", "-p", policy]
        r = subprocess.run([*prefix, *driver, str(lib), *(["canonical"] if canonical else [])], cwd=work, env=env, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
    finally:
        os.umask(old)
    assert (r.returncode == 0) == succeeds, (c.name, r.returncode, r.stdout, r.stderr)
    if succeeds:
        pack = Path(r.stdout.strip().splitlines()[-1])
        assert secret in pack.read_bytes(), "pack must contain genuine source bytes"
        assert stat.S_IMODE(pack.stat().st_mode) == 0o444
        root = explicit if explicit is not None else c / ".cache/paperlean"
        if explicit is None:
            assert stat.S_IMODE(root.stat().st_mode) == 0o700, (c.name, oct(root.stat().st_mode))
        results.append({"case": c.name, "success": True, "root_mode": oct(stat.S_IMODE(root.stat().st_mode))})
    else:
        assert not list(c.rglob("pack.paperlean")), "failed protection published private data"
        results.append({"case": c.name, "success": False, "error": r.stderr.strip()})


# New system-cache homes are created privately too, without changing existing parents.
for mask in [0o022, 0o000]:
    c, home, root = case("new-" + oct(mask))
    run(c, mask)
    assert stat.S_IMODE(home.stat().st_mode) == 0o700
    assert stat.S_IMODE(c.stat().st_mode) == 0o755

c, home, root = case("old-root")
root.mkdir(parents=True)
home.chmod(0o755)
root.chmod(0o755)
run(c)
assert stat.S_IMODE(home.stat().st_mode) == 0o755

c, home, root = case("explicit-shared")
shared = c / "shared"
shared.mkdir(mode=0o755)
shared.chmod(0o755)
run(c, explicit=shared)
assert stat.S_IMODE(shared.stat().st_mode) == 0o755
assert not home.exists()

c, home, root = case("owned-alias")
home.mkdir()
target = c / "relocated"
target.mkdir()
target.chmod(0o755)
root.symlink_to(target, target_is_directory=True)
link_inode = root.lstat().st_ino
run(c)
assert root.is_symlink() and root.lstat().st_ino == link_inode
assert stat.S_IMODE(target.stat().st_mode) == 0o700

# Public callers may canonicalize the automatic root before entering cache APIs.
c, home, root = case("canonical-owned-alias")
home.mkdir()
target = c / "relocated"
target.mkdir()
target.chmod(0o755)
root.symlink_to(target, target_is_directory=True)
run(c, canonical=True)
assert root.is_symlink() and stat.S_IMODE(target.stat().st_mode) == 0o700

for kind in ["file", "fifo", "dangling"]:
    c, home, root = case("invalid-" + kind)
    home.mkdir()
    if kind == "file": root.write_text("keep")
    elif kind == "fifo": os.mkfifo(root)
    else: root.symlink_to(c / "missing")
    original = root.lstat()
    run(c, succeeds=False)
    assert root.lstat().st_ino == original.st_ino
    if kind == "file": assert root.read_text() == "keep"

c, home, root = case("unsafe-parent")
home.mkdir()
home.chmod(0o777)
run(c, succeeds=False)
assert not root.exists() and stat.S_IMODE(home.stat().st_mode) == 0o777

# An owned alias to an unowned system directory is refused before any chmod/publication.
foreign = next((p for p in [Path("/var/empty"), Path("/usr")] if p.is_dir() and p.stat().st_uid != os.geteuid()), None)
if foreign is not None:
    c, home, root = case("unowned-target")
    home.mkdir()
    root.symlink_to(foreign, target_is_directory=True)
    before = foreign.stat()
    run(c, succeeds=False)
    after = foreign.stat()
    assert (before.st_ino, before.st_mode, before.st_ctime_ns) == (after.st_ino, after.st_mode, after.st_ctime_ns)

if sys.platform == "darwin":
    if shutil.which("sandbox-exec"):
        # No fchmod is necessary for an already-private root. Child publication is
        # still allowed, and the sandbox makes any attempted mode rewrite fail.
        c, home, root = case("private-mode-denied")
        root.mkdir(parents=True)
        root.chmod(0o700)
        run(c, deny_mode=True)

        c, home, root = case("migration-mode-denied")
        root.mkdir(parents=True)
        root.chmod(0o755)
        run(c, deny_mode=True, succeeds=False)
        assert stat.S_IMODE(root.stat().st_mode) == 0o755

    c, home, root = case("acl-preserved-deny")
    root.mkdir(parents=True)
    owner = pwd.getpwuid(os.geteuid()).pw_name
    subprocess.run(["/bin/chmod", "+a", "everyone allow list,search,readattr", str(root)], check=True)
    subprocess.run(["/bin/chmod", "+a", f"user:{owner} deny delete", str(root)], check=True)
    before = subprocess.check_output(["/bin/ls", "-lde", str(root)], text=True)
    assert "allow" in before and "deny delete" in before
    run(c)
    after = subprocess.check_output(["/bin/ls", "-lde", str(root)], text=True)
    assert "allow" not in after and "deny delete" in after

    # An explicit owner grant can legitimately precede a deny applying to everyone.
    # Removing that grant would break an already-private, usable cache.
    c, home, root = case("acl-owner-grant")
    root.mkdir(parents=True)
    root.chmod(0o700)
    rights = "list,search,add_file,add_subdirectory,delete_child,readattr,writeattr,readextattr,writeextattr,readsecurity,writesecurity,chown"
    subprocess.run(["/bin/chmod", "+a", "everyone deny " + rights, str(root)], check=True)
    subprocess.run(["/bin/chmod", "+a#", "0", f"user:{owner} allow " + rights, str(root)], check=True)
    before_acl = subprocess.check_output(["/bin/ls", "-lde", str(root)], text=True).splitlines()[1:]
    run(c)
    after_acl = subprocess.check_output(["/bin/ls", "-lde", str(root)], text=True).splitlines()[1:]
    assert before_acl == after_acl and any("allow" in x for x in after_acl)

    # Mode0755 alone is insufficient if a parent ACL grants another principal the
    # ability to create/replace its child entries. Reject without modifying that ACL.
    for permission in ["add_subdirectory", "delete_child"]:
        c, home, root = case("acl-parent-" + permission)
        home.mkdir()
        home.chmod(0o755)
        subprocess.run(["/bin/chmod", "+a", "everyone allow " + permission, str(home)], check=True)
        before_acl = subprocess.check_output(["/bin/ls", "-lde", str(home)], text=True).splitlines()[1:]
        run(c, succeeds=False)
        assert not root.exists()
        assert stat.S_IMODE(home.stat().st_mode) == 0o755
        assert before_acl == subprocess.check_output(["/bin/ls", "-lde", str(home)], text=True).splitlines()[1:]

    for label, grant in [("readonly", "everyone allow list,search,readattr"),
                         ("owner", f"user:{owner} allow add_file,add_subdirectory,delete_child")]:
        c, home, root = case("acl-parent-" + label)
        home.mkdir()
        home.chmod(0o755)
        subprocess.run(["/bin/chmod", "+a", grant, str(home)], check=True)
        before_acl = subprocess.check_output(["/bin/ls", "-lde", str(home)], text=True).splitlines()[1:]
        run(c)
        assert stat.S_IMODE(home.stat().st_mode) == 0o755
        assert before_acl == subprocess.check_output(["/bin/ls", "-lde", str(home)], text=True).splitlines()[1:]

    c, home, root = case("acl-owner-deny")
    root.mkdir(parents=True)
    subprocess.run(["/bin/chmod", "+a", f"user:{owner} deny add_file,add_subdirectory", str(root)], check=True)
    run(c, succeeds=False)
    after = subprocess.check_output(["/bin/ls", "-lde", str(root)], text=True)
    assert "deny" in after and "add_file" in after and "add_subdirectory" in after

assert stat.S_IMODE(source.stat().st_mode) == 0o700
(work / "receipt.json").write_text(json.dumps(results, indent=2))
# The assertions above require deny ACLs to survive protection. Remove only the
# ACLs introduced by these scratch cases so the surrounding test harness can clean up.
if sys.platform == "darwin":
    for case_dir in work.iterdir():
        if not case_dir.name.startswith("acl-"):
            continue
        for path in [case_dir / ".cache/paperlean", case_dir / ".cache"]:
            if path.is_dir() and not path.is_symlink():
                subprocess.run(["/bin/chmod", "-N", str(path)], check=True)

print(json.dumps(results, indent=2))
