# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Demand-byte counts and descriptor identity regressions, without elapsed-time assertions."""
from pathlib import Path
import json
import os
import shutil
import subprocess
import sys
import time

HELPER = Path(sys.argv[1]).resolve()
ROOT = Path(sys.argv[2]).resolve()
ROOT.mkdir(parents=True)
ENV = os.environ.copy()
for key in ('LEAN_OLEAN_PACK', 'LEAN_IMPORT_IMAGE', 'PAPERLEAN_NATIVE_LIBS',
            'PAPERLEAN_ACCELERATE', 'PAPERLEAN_SETUP_INDEX_READS'):
    ENV.pop(key, None)
EVENTS = ROOT / 'reads.tsv'


def command(*args):
    return [str(HELPER), *map(str, args)]


def run(*args, env=None, ok=True, timeout=120):
    r = subprocess.run(command(*args), env=env or ENV, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
    if ok:
        assert r.returncode == 0, (args, r.stdout, r.stderr)
    else:
        assert r.returncode > 0, (args, r.returncode, r.stdout, r.stderr)
    return r


def emit(where, size=16, mode='receipt'):
    lines = run('emit', where, size, mode).stdout.splitlines()
    assert len(lines) == 2, lines
    return tuple(map(Path, lines))


def read(setup, demand=True):
    EVENTS.write_text('')
    r = run('read', setup, env=dict(ENV, PAPERLEAN_SETUP_INDEX_READS=str(EVENTS)))
    assert json.loads(r.stdout) == json.loads(Path(str(setup) + '.expected').read_text())
    events = EVENTS.read_text().splitlines()
    if demand:
        assert len(events) == 1, events
        _, copied, records, total = events[0].split('\t')
        return int(copied), int(records), int(total)
    assert not events, events


# The reached graph is four records while the unrelated library grows by two orders of magnitude.
counts = []
for size in (32, 512, 8192, 16384, 65536):
    index, setup = emit(ROOT / f'scale-{size}', size)
    demand = index.stat().st_size > 128 * 1024
    assert Path(str(index) + '.validated').is_file() == demand
    result = read(setup, demand=demand)
    if demand: counts.append(result)
assert len(counts) >= 2
assert all(records == 4 for _, records, _ in counts), counts
assert len({copied for copied, _, _ in counts}) == 1, counts
assert counts[-1][2] > counts[0][2], counts
print('demand (copied bytes, reached records, total bytes):', counts)

# A newer immutable generation does not replace an older one in the same build directory.
_, older = emit(ROOT / 'generations', 16)
_, newer = emit(ROOT / 'generations', 16384)
read(older, demand=False)
read(newer)

# Independent v1 input and a missing/copy-stale receipt use the original whole-file validation.
_, independent = emit(ROOT / 'independent', mode='plain')
read(independent, demand=False)
file, setup = emit(ROOT / 'no-receipt', 16384)
Path(str(file) + '.validated').unlink()
read(setup, demand=False)
file, setup = emit(ROOT / 'copied-source', 16384)
copy = ROOT / 'copied'
shutil.copytree(file.parent, copy)
cloned_setup = copy / setup.name
value = json.loads(cloned_setup.read_text())
# The anonymous index reference remains a full-path entry under "[anonymous]".
for key, artifact in value['importArts'].items():
    if key == '[anonymous]':
        artifact[0][0] = str(copy / file.name)
cloned_setup.write_text(json.dumps(value))
read(cloned_setup, demand=False)

# Pre-existing byte damage invalidates the receipt and must fail the full content-hash fallback.
for size in (16, 16384):
    file, setup = emit(ROOT / f'damaged-{size}', size)
    file.chmod(0o644)
    with file.open('ab') as f:
        f.write(b'damage')
    r = run('read', setup, ok=False)
    assert 'contents do not have the hash' in r.stderr + r.stdout, r

# Unreceipted v1 references may follow a regular symlink. A FIFO, directly or
# behind that symlink, must fail without waiting for a writer.
if os.name == 'posix':
    file, setup = emit(ROOT / 'v1-file-types', mode='plain')
    target = file.with_name('regular-target')
    file.rename(target)
    file.symlink_to(target)
    read(setup, demand=False)
    original = target.read_bytes()
    target.write_bytes(original[:-1])
    r = run('read', setup, ok=False)
    assert 'contents do not have the hash' in r.stderr + r.stdout, r
    target.unlink()
    os.mkfifo(target)
    run('read', setup, ok=False, timeout=5)
    file.unlink()
    os.mkfifo(file)
    run('read', setup, ok=False, timeout=5)

# Mutations after opening must fail safely through actual FD-bound read/final-check entry points.
for mutation in ('replace', 'truncate', 'delete'):
    for operation in ('check', 'read'):
        home = ROOT / f'{mutation}-{operation}'
        file, _ = emit(home, 16384)
        gate = home / 'gate'
        gate.mkdir()
        child = subprocess.Popen(command('held', file, gate, operation), env=ENV,
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            for _ in range(1200):
                if (gate / 'opened').exists():
                    break
                assert child.poll() is None, child.communicate()
                time.sleep(0.05)
            assert (gate / 'opened').exists(), 'descriptor gate timed out'
            if mutation == 'replace':
                replacement = home / 'replacement'
                replacement.write_bytes(file.read_bytes())
                replacement.chmod(0o444)
                replacement.replace(file)
            elif mutation == 'truncate':
                file.chmod(0o644)
                file.write_bytes(b'')
            else:
                file.unlink()
            (gate / 'release').touch()
            stdout, stderr = child.communicate(timeout=120)
            assert child.returncode > 0, (mutation, operation, child.returncode, stdout, stderr)
            assert 'generation changed' in stdout + stderr, (stdout, stderr)
        finally:
            if child.poll() is None:
                child.kill()
                child.wait()
print('v1 fallback, immutable generations and opened-descriptor mutation checks passed')
