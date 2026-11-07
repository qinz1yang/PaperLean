# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Bounded partial-cache repair and retained-object race regressions. Run only in test scratch."""
from pathlib import Path
import json
import os
import shutil
import re
import subprocess
import sys
import time

ROOT = Path(sys.argv[2]).resolve()
ROOT.mkdir(parents=True, exist_ok=True)
ENV = os.environ.copy()
# Apple's Python launcher adds SDK and search paths to its children's environment.
# Start default admission cases in the same environment as a direct shell invocation.
for var in ('CPATH', 'LIBRARY_PATH', 'SDKROOT', 'PAPERLEAN_IMPORT', 'PAPERLEAN_IMPORT_TIMING', 'LEAN_OLEAN_PACK',
            'LEAN_IMPORT_IMAGE', 'PAPERLEAN_NATIVE_LIBS', 'ELAN_TOOLCHAIN', 'LEAN_CC',
            'PAPERLEAN_ACCELERATE', 'PAPERLEAN_EXACT', 'PAPERLEAN_UNIT_BYTES',
            'PAPERLEAN_EVAL_SECONDS', 'PAPERLEAN_EVAL_EVENTS',
            'PAPERLEAN_IMAGE_VERIFY_EVENTS', 'PAPERLEAN_NATIVE_REPAIR_EVENTS'):
    ENV.pop(var, None)
ENV['PAPERLEAN_CACHE_DIR'] = str(ROOT / 'cache')
ENV['XDG_CACHE_HOME'] = str(ROOT / 'xdg')


def write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


def run(ws, args, env=None, timeout=180):
    result = subprocess.run(['lake', *args], cwd=ws, env=env or ENV, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)
    print(result.stdout, end='', flush=True)
    if result.returncode:
        raise AssertionError(f'{args}: exit {result.returncode}')
    return result.stdout


def setup(home, two=False):
    dep, ws = home / 'dep', home / 'root'
    write(dep / 'lakefile.toml', 'name = "dep"\ndefaultTargets = ["Dep"]\n'
          '[[lean_lib]]\nname = "Dep"\nglobs = ["Dep.+"]\n')
    write(dep / 'Dep/A.lean', 'def a (n : Nat) : Nat := n + 1\n')
    if two:
        write(dep / 'Dep/B.lean', 'def b (n : Nat) : Nat := n + 3\n')
    write(ws / 'lakefile.toml', 'name = "root"\ndefaultTargets = ["Root"]\n'
          '[[require]]\nname = "dep"\npath = "../dep"\n[[lean_lib]]\nname = "Root"\n')
    imports = 'import Dep.A\n' + ('import Dep.B\n' if two else '')
    write(ws / 'Root.lean', imports)
    write(ws / 'Use.lean', imports + '#eval a 41\n')
    run(ws, ['build'])
    return dep, ws


def prepared(ws):
    return json.loads((ws / '.lake/paperlean/env.json').read_text())


def paths(ws):
    d = prepared(ws)
    lib = next(l for l in d['libs'] if l['pkg'] == 'dep')
    cache = Path(d['cache'])
    return d, lib, cache / lib['entry'], cache / lib['lib'], cache / lib['manifest']


def equivalent(ws, env=ENV, libraries=1):
    plain = run(ws, ['lean', 'Use.lean'], env)
    for exact in (False, True):
        use = dict(env, PAPERLEAN_ACCELERATE='1', PAPERLEAN_IMPORT_TIMING='1')
        if exact:
            use['PAPERLEAN_EXACT'] = '1'
        text = run(ws, ['lean', 'Use.lean'], use)
        counts = re.findall(r'^paperlean-timing native libs=(\d+) ', text, re.MULTILINE)
        if libraries:
            assert str(libraries) in counts, text
        else:
            # An empty native list bypasses the verifier; importing still emits timing records.
            assert not prepared(ws)['native'], prepared(ws)
            assert 'paperlean-timing start ' in text and all(n == '0' for n in counts), text
        output = '\n'.join(line for line in text.splitlines() if not line.startswith('paperlean-')) + '\n'
        assert output == plain, (output, plain)
        assert 'warning:' not in text, text


def image_reporting(ws):
    events = ROOT / 'image-verify.events'
    env = dict(ENV, PAPERLEAN_IMAGE_VERIFY_EVENTS=str(events))
    run(ws, ['paperlean', 'prepare', '-j', '1'], env)
    assert events.is_file() and events.read_text(), 'prepare did not fully verify its image'
    events.write_text('')
    for _ in range(2):
        output = run(ws, ['paperlean', 'build'], env)
        assert ', an import image' in output, output
        assert not events.read_text(), 'an ordinary no-op build fully verified the image'
    output = run(ws, ['paperlean', 'status', '--verify'], env)
    assert events.read_text(), 'explicit status verification did not use the full verifier'
    assert 'not usable:' not in output, output


def damage():
    _, ws = setup(ROOT / 'damage')
    run(ws, ['paperlean', 'prepare', '-j', '2'])
    equivalent(ws)
    for kind in ('library', 'manifest', 'library-bytes', 'manifest-bytes', 'json',
                 'json-missing', 'json-directory', 'json-fifo', 'image', 'image-bytes'):
        d, lib, entry, image, manifest = paths(ws)
        metadata = entry / 'native.json'
        if kind == 'library':
            image.unlink()
        elif kind == 'manifest':
            manifest.unlink()
        elif kind == 'library-bytes':
            image.chmod(0o755)
            with image.open('ab') as f:
                f.write(b'damaged')
        elif kind == 'manifest-bytes':
            with manifest.open('ab') as f:
                f.write(b'damaged')
        elif kind == 'json':
            metadata.write_text('{broken')
        elif kind == 'json-missing':
            metadata.unlink()
        elif kind == 'json-directory':
            metadata.unlink()
            metadata.mkdir()
        elif kind == 'json-fifo':
            metadata.unlink()
            os.mkfifo(metadata)
        else:
            old_image = ws / '.lake/paperlean' / d['image']
            assert old_image.is_file(), 'the fixture needs a prepared image'
            if kind == 'image':
                old_image.unlink()
            else:
                old_image.chmod(0o644)
                with old_image.open('ab') as f:
                    f.write(b'damaged')
        status = run(ws, ['paperlean', 'status'], timeout=30)
        if kind.startswith('image'):
            assert ', an import image' not in status, status
        else:
            assert '1 native libraries' not in status, status
            assert 'native library of dep: 1 modules' not in status, status
        run(ws, ['paperlean', 'prepare', '-j', '2'])
        equivalent(ws)
        status = run(ws, ['paperlean', 'status', '--verify'], timeout=30)
        assert 'not usable:' not in status, status
        assert ', an import image' in status, status
    # Two workspaces repair the same entry. Key-lock rechecking must make the second reuse the winner.
    ws2 = ws.parent / 'root2'
    shutil.copytree(ws, ws2, ignore=shutil.ignore_patterns('.lake'))
    run(ws2, ['build'])
    _, _, entry, image, _ = paths(ws)
    image.unlink()
    logs = []
    children = []
    for target in (ws, ws2):
        log = (target / 'repair.log').open('w')
        logs.append(log)
        children.append(subprocess.Popen(['lake', 'paperlean', 'prepare', '-j', '1'],
                                         cwd=target, env=ENV, stdout=log, stderr=subprocess.STDOUT))
    try:
        for child in children:
            assert child.wait(timeout=180) == 0
    finally:
        for child in children:
            if child.poll() is None:
                child.kill()
                child.wait()
        for log in logs:
            log.close()
    texts = [(target / 'repair.log').read_text() for target in (ws, ws2)]
    assert sum('Compiling the native library of dep' in text for text in texts) == 1, texts
    equivalent(ws)
    equivalent(ws2)


def dependency_damage():
    home = ROOT / 'dependency-chain'
    dep, mid, top, ws = (home / p for p in ('dep', 'mid', 'top', 'root'))
    write(dep / 'lakefile.toml', 'name = "dep"\ndefaultTargets = ["Dep"]\n'
          '[[lean_lib]]\nname = "Dep"\nglobs = ["Dep.+"]\n')
    write(dep / 'Dep/A.lean', 'def a (n : Nat) : Nat := n + 1\n')
    write(mid / 'lakefile.toml', 'name = "mid"\ndefaultTargets = ["Mid"]\n'
          '[[require]]\nname = "dep"\npath = "../dep"\n[[lean_lib]]\nname = "Mid"\n')
    write(mid / 'Mid.lean', 'import Dep.A\ndef middle (n : Nat) : Nat := a n\n')
    write(top / 'lakefile.toml', 'name = "top"\ndefaultTargets = ["Top"]\n'
          '[[require]]\nname = "mid"\npath = "../mid"\n[[lean_lib]]\nname = "Top"\n')
    write(top / 'Top.lean', 'import Mid\ndef upper (n : Nat) : Nat := middle n\n')
    write(ws / 'lakefile.toml', 'name = "root"\ndefaultTargets = ["Root"]\n'
          '[[require]]\nname = "top"\npath = "../top"\n[[lean_lib]]\nname = "Root"\n')
    write(ws / 'Root.lean', 'import Top\n')
    write(ws / 'Use.lean', 'import Top\n#eval upper 41\n')
    run(ws, ['build'])
    gate = home / 'gate'
    gate.mkdir()
    (gate / 'release').touch()
    env = gate_env(gate)
    run(ws, ['paperlean', 'prepare', '-j', '1'], env)
    equivalent(ws, env, libraries=3)
    for kind in ('missing', 'corrupt', 'legacy', 'wrong-meta-hash'):
        d, _, entry, _, _ = paths(ws)
        metadata = entry / 'native.json'
        if kind == 'missing':
            metadata.unlink()
        elif kind == 'corrupt':
            metadata.write_text('{broken')
        elif kind == 'wrong-meta-hash':
            record = json.loads(metadata.read_text())
            h = record['metaHash']
            assert len(h) == 32
            record['metaHash'] = ('1' if h[0] == '0' else '0') + h[1:]
            metadata.write_text(json.dumps(record))
        else:
            record = json.loads(metadata.read_text())
            record.pop('files', None)
            record.pop('dependencies', None)
            metadata.write_text(json.dumps(record))
        # Named preparation must reconstruct the bottom package and every retained importer once.
        target = 'top' if kind == 'wrong-meta-hash' else 'dep'
        output = run(ws, ['paperlean', 'prepare', '-j', '1', target], env)
        for pkg in ('dep', 'mid', 'top'):
            assert f'Compiling the native library of {pkg} ' in output, (kind, output)
        assert not any(lib.get('failed', False) for lib in prepared(ws)['libs']), output
        equivalent(ws, env, libraries=3)
    concurrent_dependency_repair(ws, env, gate)


def concurrent_dependency_repair(ws, env, gate):
    ws2 = ws.parent / 'root2'
    shutil.copytree(ws, ws2, ignore=shutil.ignore_patterns('.lake', '*.log'))
    run(ws2, ['build'])
    _, _, entry, _, _ = paths(ws)
    (entry / 'native.json').write_text('{broken')
    # Force the first repair into its C-compiler barrier while holding the full sorted lock set.
    for directory in Path(env['PAPERLEAN_CACHE_DIR']).glob('prepared/*/objects'):
        shutil.rmtree(directory)
    for marker in gate.glob('blocked-*'):
        marker.unlink()
    (gate / 'release').unlink()
    (gate / 'eval.events').write_text('')
    events = ws.parent / 'repair-events'
    events.mkdir()
    local = dict(env, PAPERLEAN_NATIVE_REPAIR_EVENTS=str(events))
    logs, handles, children = [], [], []
    try:
        for target in (ws, ws2):
            path = target / 'dependency-repair.log'
            handle = path.open('w')
            logs.append(path)
            handles.append(handle)
            children.append(subprocess.Popen(['lake', 'paperlean', 'prepare', '-j', '1'],
                cwd=target, env=local, stdout=handle, stderr=subprocess.STDOUT))
            if target == ws:
                wait_blocked(gate, path, children[0])
                first = set(events.glob('scheduled-*.json'))
                assert len(first) == 1
        second_marker = None
        for _ in range(1200):
            more = set(events.glob('scheduled-*.json')) - first
            if more:
                assert len(more) == 1
                second_marker = more.pop()
                break
            assert children[1].poll() is None, logs[1].read_text()
            time.sleep(0.1)
        assert second_marker is not None, 'second repair never reached its lock set'
        assert json.loads(second_marker.read_text()) == ['dep', 'mid', 'top']
        # The second process has scheduled the closure while the first still owns its entry locks.
        (gate / 'release').touch()
        for child in children:
            assert child.wait(timeout=180) == 0
        rechecked = events / second_marker.name.replace('scheduled-', 'rechecked-')
        assert json.loads(rechecked.read_text()) == [], 'the concurrent winner was rebuilt'
    finally:
        (gate / 'release').touch()
        for child in children:
            if child.poll() is None:
                child.kill()
                child.wait()
        for handle in handles:
            handle.close()
    texts = [path.read_text() for path in logs]
    for pkg in ('dep', 'mid', 'top'):
        assert sum(f'Compiling the native library of {pkg} ' in text for text in texts) == 1, texts
    equivalent(ws, env, libraries=3)
    equivalent(ws2, env, libraries=3)


def gate_env(gate, two=False):
    return dict(ENV, PAPERLEAN_NATIVE_COMPILER_GATE=str(gate),
                PAPERLEAN_NATIVE_COMPILER_GATE_INPUT='/Dep/A.c',
                PAPERLEAN_EVAL_EVENTS=str(gate / 'eval.events'),
                PAPERLEAN_UNIT_BYTES='4000000' if two else '0')


def wait_blocked(gate, log, child, count=1, evaluated=True):
    for _ in range(1200):
        if child.poll() is not None:
            raise AssertionError(('prepare ended before the compiler gate', log.read_text()))
        ready = len(list(gate.glob('blocked-*'))) >= count
        events = gate / 'eval.events'
        done = events.is_file() and 'done' in events.read_text().splitlines()
        if ready and (not evaluated or done):
            return
        time.sleep(0.1)
    raise AssertionError(('compiler gate timed out', log.read_text()))


def race_case(two):
    home = ROOT / ('unit' if two else 'single')
    dep, ws = setup(home, two)
    original = dep / '.lake/build/ir/Dep/A.c'
    old = original.read_bytes()
    write(dep / 'Dep/A.lean', 'def a (n : Nat) : Nat := n + 2\n')
    run(ws, ['build'])
    changed = original.read_bytes()
    assert changed != old
    write(dep / 'Dep/A.lean', 'def a (n : Nat) : Nat := n + 1\n')
    run(ws, ['build'])
    assert original.read_bytes() == old
    gate = home / 'gate'
    gate.mkdir()
    env = gate_env(gate, two)
    logfile = home / 'rejected.log'
    with logfile.open('w') as log:
        child = subprocess.Popen(['lake', 'paperlean', 'prepare', '-j', '1'],
                                 cwd=ws, env=env, stdout=log, stderr=subprocess.STDOUT)
        try:
            wait_blocked(gate, logfile, child)
            first_input = (gate / 'calls').read_text().splitlines()[0]
            assert ('-unit-' in first_input) == two, first_input
            # Change exactly the C file that the blocked compiler is about to read.
            original.write_bytes(changed)
            (gate / 'release').touch()
            assert child.wait(timeout=180) == 0, logfile.read_text()
        finally:
            if child.poll() is None:
                child.kill()
                child.wait()
            original.write_bytes(old)
    print(logfile.read_text(), end='')
    # Keep every shared object, including any poisoned one. Only native entries are removed.
    cache = Path(ENV['PAPERLEAN_CACHE_DIR'])
    for entry in cache.glob('prepared/*/native/dep-*'):
        shutil.rmtree(entry)
    before = len((gate / 'calls').read_text().splitlines())
    run(ws, ['paperlean', 'prepare', '-j', '1'], env)
    after = len((gate / 'calls').read_text().splitlines())
    equivalent(ws, env)
    assert after > before, 'the rejected C input left a reusable shared object'
    if two:
        publishers(ws, env, gate, cache)


def publishers(ws, env, gate, cache):
    ws2 = ws.parent / 'root2'
    shutil.copytree(ws, ws2, ignore=shutil.ignore_patterns('.lake', '*.log'))
    run(ws2, ['build'])
    for directory in cache.glob('prepared/*/objects'):
        shutil.rmtree(directory)
    for directory in cache.glob('prepared/*/native/dep-*'):
        shutil.rmtree(directory)
    for marker in gate.glob('blocked-*'):
        marker.unlink()
    (gate / 'release').unlink()
    children, handles, logs = [], [], []
    # Different native-entry keys allow both compilers to reach the same object key concurrently.
    for target, seconds in ((ws, '10'), (ws2, '11')):
        logfile = target / 'publisher.log'
        log = logfile.open('w')
        logs.append(logfile)
        handles.append(log)
        local = dict(env, PAPERLEAN_EVAL_SECONDS=seconds)
        children.append(subprocess.Popen(['lake', 'paperlean', 'prepare', '-j', '1'],
                                         cwd=target, env=local, stdout=log, stderr=subprocess.STDOUT))
    try:
        wait_blocked(gate, logs[0], children[0], count=2, evaluated=False)
        (gate / 'release').touch()
        for child in children:
            assert child.wait(timeout=180) == 0
    finally:
        (gate / 'release').touch()
        for child in children:
            if child.poll() is None:
                child.kill()
                child.wait()
        for handle in handles:
            handle.close()
    for target in (ws, ws2):
        equivalent(target, env)


def identity(path):
    s = path.stat()
    return s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns


def aba_case(two):
    home = ROOT / ('aba-unit' if two else 'aba-single')
    dep, ws = setup(home, two)
    original = dep / '.lake/build/ir/Dep/A.c'
    old = original.read_bytes()
    write(dep / 'Dep/A.lean', 'def a (n : Nat) : Nat := n + 2\n')
    run(ws, ['build'])
    other = original.read_bytes()
    assert old != other
    write(dep / 'Dep/A.lean', 'def a (n : Nat) : Nat := n + 1\n')
    run(ws, ['build'])
    assert original.read_bytes() == old
    stamp = identity(original)
    alternate = original.parent.with_name('alternate')
    saved = original.parent.with_name('saved')
    shutil.copytree(original.parent, alternate)
    (alternate / 'A.c').write_bytes(other)
    gate = home / 'gate'
    gate.mkdir()
    (gate / 'restore-required').touch()
    env = gate_env(gate, two)
    logfile = home / 'aba.log'
    with logfile.open('w') as log:
        child = subprocess.Popen(['lake', 'paperlean', 'prepare', '-j', '1'],
                                 cwd=ws, env=env, stdout=log, stderr=subprocess.STDOUT)
        try:
            wait_blocked(gate, logfile, child)
            first = (gate / 'calls').read_text().strip()
            assert ('-unit-' in first) == two, first
            original.parent.rename(saved)
            try:
                alternate.rename(original.parent)
                try:
                    assert original.read_bytes() == other
                    (gate / 'release').touch()
                    for _ in range(1200):
                        if (gate / 'compiled').exists():
                            break
                        assert child.poll() is None, logfile.read_text()
                        time.sleep(0.1)
                    else:
                        raise AssertionError(('compiler did not finish', logfile.read_text()))
                    assert (gate / 'compiled').read_text() == '0', logfile.read_text()
                finally:
                    original.parent.rename(alternate)
            finally:
                saved.rename(original.parent)
                (gate / 'restored').touch()
            assert identity(original) == stamp, 'the sampled original file identity changed'
            assert child.wait(timeout=180) == 0, logfile.read_text()
        finally:
            (gate / 'release').touch()
            (gate / 'restored').touch()
            if child.poll() is None:
                child.kill()
                child.wait()
    print(logfile.read_text(), end='', flush=True)
    # Keep every retained object. Force a native relink from those objects and compare both native
    # loading modes against the interpreter. This catches a successful publish under the wrong key.
    cache = Path(ENV['PAPERLEAN_CACHE_DIR'])
    objects = list(cache.glob('prepared/*/objects/*.o'))
    assert objects, 'expected a retained object'
    for entry in cache.glob('prepared/*/native/dep-*'):
        shutil.rmtree(entry)
    before = (gate / 'calls').read_text()
    run(ws, ['paperlean', 'prepare', '-j', '1'], env)
    plain = run(ws, ['lean', 'Use.lean'], env)
    assert (gate / 'calls').read_text() == before, 'retained object was rebuilt'
    assert plain.strip() == '42', plain
    equivalent(ws, env)



def cross_worktree():
    home = ROOT / 'independent'
    first_dep, first = setup(home / 'first', True)
    second_dep, second = setup(home / 'second', True)
    assert first_dep.resolve() != second_dep.resolve()
    gate = home / 'gate'
    gate.mkdir()
    (gate / 'release').touch()
    env = gate_env(gate, True)
    libraries = []
    objects = None
    for dep, ws in ((first_dep, first), (second_dep, second)):
        write(ws / 'Use.lean', 'import Dep.A\nimport Dep.B\nexample : a 41 = 42 := rfl\n#eval a 41\n')
        text = run(ws, ['paperlean', 'prepare', '-j', '1'], env)
        _, lib, _, _, _ = paths(ws)
        assert lib['modules'] == 2, lib
        libraries.append(lib['entry'])
        cache = Path(env['PAPERLEAN_CACHE_DIR'])
        found = {str(p): identity(p) for p in cache.glob('prepared/*/objects/*.o')}
        assert found
        if objects is None:
            objects = found
            calls = (gate / 'calls').read_text()
            assert '-unit-' in calls, calls
        else:
            assert libraries[0] == libraries[1], libraries
            assert 'from the cache' in text, text
            assert found == objects, (found, objects)
            assert (gate / 'calls').read_text() == calls
        equivalent(ws, env)
    # Force a link in the distinct checkout, retaining every object.
    _, _, entry, _, _ = paths(second)
    shutil.rmtree(entry)
    run(second, ['paperlean', 'prepare', '-j', '1'], env)
    assert (gate / 'calls').read_text() == calls
    equivalent(second, env)


def checked_c_trace(c, dep, ws):
    helper = ws / 'CHash.lean'
    write(helper, 'import Lake.Build.Trace\n'
          'def main (args : List String) : IO Unit := do\n'
          '  let [p] := args | throw (IO.userError "expected one C file")\n'
          '  IO.println (← Lake.computeFileHash p)\n')
    p = subprocess.run(['lean', '--run', str(helper), str(c)], cwd=ws, env=ENV,
                       capture_output=True, text=True, timeout=60, check=True)
    digest = p.stdout.strip()
    assert len(digest) == 16 and all(x in '0123456789abcdef' for x in digest), p.stdout
    trace = dep / '.lake/build/lib/lean/Dep/A.trace'
    j = json.loads(trace.read_text())
    assert j['outputs']['c'].endswith('.c'), j
    j['outputs']['c'] = digest + '.c'
    trace.write_text(json.dumps(j))
    c.with_suffix('.c.hash').write_text(digest)


def unbound_inputs():
    dep, ws = setup(ROOT / 'unbound', True)
    orig = dep / '.lake/build/ir/Dep/A.c'
    source = orig.read_bytes()
    local = orig.parent / 'local'
    write(local / 'nested.h', '#define EXPECTED_LOCAL 42\n')
    write(local / 'header.h', '#include "nested.h"\n')
    prefix = ('#include "local/header.h"\n'
              '_Static_assert(EXPECTED_LOCAL == 42, "wrong quoted header");\n'
              '_Static_assert(__builtin_strcmp(__FILE__, ' + json.dumps(str(orig)) +
              ') == 0, "wrong module pathname");\n'
              '_Static_assert(__builtin_strcmp(__BASE_FILE__, ' + json.dumps(str(orig)) +
              ') == 0, "wrong main pathname");\n')
    temp = orig.with_suffix('.c.replacement')
    temp.write_bytes(prefix.encode() + source)
    temp.replace(orig)
    checked_c_trace(orig, dep, ws)
    control_object = ws / 'original-path.o'
    subprocess.run(['leanc', '-g', '-c', str(orig), '-o', str(control_object)],
                   cwd=ws, env=ENV, check=True, timeout=60)
    assert control_object.stat().st_size
    if sys.platform == 'darwin':
        dump = subprocess.run(['dwarfdump', '--debug-info', '--debug-line', str(control_object)],
                              text=True, capture_output=True, check=True)
        assert orig.name in dump.stdout and str(orig.parent) in dump.stdout, dump.stdout[:600]
    run(ws, ['paperlean', 'prepare', '-j', '1'])
    d, lib, _, _, _ = paths(ws)
    assert lib['modules'] == 1 and 'outside the relocatable generated-C profile' in json.dumps(d), d
    write(ws / 'Use.lean', 'import Dep.A\nimport Dep.B\nexample : a 41 = 42 := rfl\n#eval a 41\n')
    equivalent(ws)
    write(local / 'nested.h', '#define EXPECTED_LOCAL 99\n')
    p = subprocess.run(['leanc', '-c', str(orig), '-o', str(control_object)], cwd=ws, env=ENV,
                       capture_output=True, text=True, timeout=60)
    assert p.returncode and 'wrong quoted header' in p.stderr, p
    run(ws, ['paperlean', 'prepare', '-j', '1'])
    d, lib, _, _, _ = paths(ws)
    assert lib['modules'] == 1 and 'outside the relocatable generated-C profile' in json.dumps(d), d
    equivalent(ws)
    # Supplying a project-local include or SDK override must not reuse the default entry.
    _, _, admitted_entry, admitted_image, admitted_manifest = paths(ws)
    admitted_files = {p: identity(p) for p in (admitted_image, admitted_manifest)}
    for key in ('CPATH', 'SDKROOT'):
        override = ws / ('override-' + key)
        override.mkdir()
        env = dict(ENV, **{key: str(override)})
        run(ws, ['paperlean', 'prepare', '-j', '1'], env)
        d = prepared(ws)
        assert not d['native'] and 'unbound native inputs' in json.dumps(d), (key, d)
        assert {p: identity(p) for p in admitted_files} == admitted_files, key
        equivalent(ws, env, libraries=0)
        run(ws, ['paperlean', 'prepare', '-j', '1'], ENV)
        _, lib, entry, _, _ = paths(ws)
        assert lib['modules'] == 1 and entry == admitted_entry, lib
        assert {p: identity(p) for p in admitted_files} == admitted_files, key
    # A same-name mutable wrapper never qualifies the project for a retained native library.
    wrapper = ws / 'custom-cc'
    for body in ('exec env -u LEAN_CC leanc "$@"', 'echo "unexpected custom compiler invocation" >&2; exit 7'):
        write(wrapper, '#!/bin/sh\n' + body + '\n')
        wrapper.chmod(0o755)
        env = dict(ENV, LEAN_CC=str(wrapper))
        run(ws, ['paperlean', 'prepare', '-j', '1'], env)
        d = prepared(ws)
        assert not d['native'] and 'unbound native inputs' in json.dumps(d), d
        equivalent(ws, env, libraries=0)


def wait_metadata(gate, signal, log, child):
    for _ in range(1600):
        if (gate / signal).is_file():
            return
        assert child.poll() is None, log.read_text()
        time.sleep(0.05)
    raise AssertionError((signal, log.read_text()))


def metadata_aba():
    home = ROOT / 'metadata-aba'
    dep, ws = setup(home)
    # Produce two real .olean generations of the *same* module. The C source and
    # all trace and inventory data used by prepare are from the colliding one.
    text = ('import Lean\nopen Lean\n'
            'def a (n : Nat) : Nat := n + 1\n'
            'def shadow (_ : Name) (_ : String) : Name := `shadowed\n')
    source = dep / 'Dep/A.lean'
    write(source, text)
    run(ws, ['build'])
    directory = dep / '.lake/build/lib/lean/Dep'
    # Keep the alternate tree outside leanLibDir while its inventory is collected.
    other = home / 'other-Dep'
    saved = home / 'saved-Dep'
    shutil.copytree(directory, other)
    write(source, text.replace('def shadow', '@[export lean_name_append_after] def shadow'))
    run(ws, ['build'])
    a = directory / 'A.olean'
    assert a.read_bytes() != (other / 'A.olean').read_bytes()
    before = identity(a)
    gate = home / 'gate'
    gate.mkdir()
    env = dict(ENV, PAPERLEAN_NATIVE_METADATA_GATE=str(gate), PAPERLEAN_NATIVE_METADATA_PACKAGE='dep')
    logfile = home / 'prepare.log'
    with logfile.open('w') as log:
        child = subprocess.Popen(['lake', 'paperlean', 'prepare', '-j', '1'], cwd=ws,
                                 env=env, stdout=log, stderr=subprocess.STDOUT)
        try:
            wait_metadata(gate, 'verified', logfile, child)
            directory.rename(saved)
            try:
                other.rename(directory)
                try:
                    (gate / 'replaced').touch()
                    wait_metadata(gate, 'sampled', logfile, child)
                finally:
                    directory.rename(other)
            finally:
                saved.rename(directory)
                (gate / 'restored').touch()
            assert identity(a) == before
            assert child.wait(timeout=180) == 0, logfile.read_text()
        finally:
            (gate / 'replaced').touch()
            (gate / 'restored').touch()
            if child.poll() is None:
                child.kill()
                child.wait()
    log = logfile.read_text()
    assert 'PaperLean does not support `@[export lean_name_append_after]` (in Dep.A)' in log, log
    lib = next(l for l in prepared(ws)['libs'] if l['pkg'] == 'dep')
    assert lib.get('failed') and not lib['entry'], lib
    assert not lib['manifest'] and not lib['lib'], lib
    equivalent(ws, libraries=0)


def metadata_membership():
    home = ROOT / 'metadata-membership'
    dep, ws = setup(home, True)
    # A is a module with private/server parts, B a legacy module with one .olean.
    write(dep / 'Dep/A.lean', 'module\npublic def a (n : Nat) := n + 1\n'
          'public meta def acceptedMeta (n : Nat) := n + 2\n')
    write(dep / 'Dep/B.lean', 'meta def omittedMeta (n : Nat) := n + 3\n')
    run(ws, ['build'])
    artifacts = dep / '.lake/build/lib/lean/Dep'
    assert (artifacts / 'A.olean.private').is_file() and not (artifacts / 'B.olean.private').exists()
    # The module has a perfectly readable .olean, but removing its C excludes it from
    # the linked set. Its declarations must never authorize another module's meta call.
    b_c = dep / '.lake/build/ir/Dep/B.c'
    b_c.unlink()
    run(ws, ['paperlean', 'prepare', '-j', '1'])
    _, lib, entry, _, _ = paths(ws)
    assert lib['modules'] == 1, lib
    meta = entry / 'meta-symbols.json'
    syms = json.loads(meta.read_text())
    assert any('acceptedMeta' in name for name in syms) and not any('omittedMeta' in name for name in syms), syms
    receipt = json.loads((entry / 'native.json').read_text())
    assert any(key.endswith('/meta-symbols.json') for key, _ in receipt['files'])
    assert len(receipt['metaHash']) == 32
    # Ordinary health/status refuses a mutated symbol payload, and a repair reconstructs it.
    original = meta.read_bytes()
    meta.write_text(json.dumps(syms + ['lp_dep_omittedMeta']))
    status = run(ws, ['paperlean', 'status'])
    assert 'native library of dep: 1 modules' not in status, status
    run(ws, ['paperlean', 'prepare', '-j', '1', 'dep'])
    assert meta.read_bytes() == original
    # Removing a required optional companion prevents A entering the linked set too.
    (artifacts / 'A.olean.private').unlink()
    run(ws, ['paperlean', 'prepare', '-j', '1', 'dep'])
    lib = next(l for l in prepared(ws)['libs'] if l['pkg'] == 'dep')
    assert lib['modules'] == 0, lib


def retained_meta_symbols():
    import struct
    home = ROOT / 'retained-meta'
    alpha, mid, ws = (home / n for n in ('alpha', 'mid', 'root'))
    write(alpha / 'lakefile.toml', 'name = "alpha"\ndefaultTargets = ["Alpha"]\n'
          '[[lean_lib]]\nname = "Alpha"\n')
    write(mid / 'lakefile.toml', 'name = "mid"\ndefaultTargets = ["Mid"]\n'
          '[[require]]\nname = "alpha"\npath = "../alpha"\n[[lean_lib]]\nname = "Mid"\n')
    write(ws / 'lakefile.toml', 'name = "root"\ndefaultTargets = ["Root"]\n'
          '[[require]]\nname = "mid"\npath = "../mid"\n[[lean_lib]]\nname = "Root"\n')
    alpha_src = 'module\n@[noinline] public def externalCode (n : Nat) : Nat := n + 1\n'
    mid_src = ('module\npublic meta import Alpha\n'
               '@[noinline] public meta def callsExternal (n : Nat) : Nat := externalCode n + 5\n')
    write(alpha / 'Alpha.lean', alpha_src)
    write(mid / 'Mid.lean', mid_src)
    write(ws / 'Root.lean', 'import Mid\n')
    write(ws / 'Use.lean', 'import Mid\n#eval callsExternal 1\n')

    def view():
        d = prepared(ws)
        dep = next(l for l in d['libs'] if l['pkg'] == 'alpha')
        importer = next(l for l in d['libs'] if l['pkg'] == 'mid')
        assert dep['modules'] == 1 and importer['modules'] == 1, (dep, importer)
        raw = (Path(d['cache']) / importer['manifest']).read_bytes()
        # `side_file_header.header_size`, followed by the first `native_module`
        # (there is just Mid). Its two meta capability bits are tested independently.
        assert raw.startswith(b'PAPERLEAN\0')
        header = struct.unpack_from('=I', raw, 136)[0]
        flags = struct.unpack_from('=I', raw, header + 32)[0]
        return dep['entry'], importer['entry'], flags & (128 | 256)

    run(ws, ['build'])
    run(ws, ['paperlean', 'prepare', '-j', '1'])
    a0, m0, flags = view()
    assert flags == 0, flags
    # A second workspace generation declares the exact same callable C symbol as meta.
    # Named preparation of Mid keeps the original Alpha library. Its symbol receipt
    # must continue to exclude the symbol, regardless of the current Alpha.olean.
    write(alpha / 'Alpha.lean', alpha_src.replace('public def', 'public meta def'))
    write(mid / 'Mid.lean', mid_src + 'public meta def generation (n : Nat) := n + 7\n')
    run(ws, ['build'])
    run(ws, ['paperlean', 'prepare', '-j', '1', 'mid'])
    a1, m1, flags = view()
    assert a0 == a1 and m0 != m1 and flags == 0, (a0, a1, m0, m1, flags)
    # Explicitly rebuilding Alpha permits that same symbol. The importer is rebuilt
    # against its new dependency and both flags become true.
    run(ws, ['paperlean', 'prepare', '-j', '1', 'alpha'])
    a2, m2, flags = view()
    assert a1 != a2 and m1 != m2 and flags == 384, (a1, a2, m1, m2, flags)
    plain = run(ws, ['lean', 'Use.lean'])
    assert plain.strip() == '7', plain
    for exact in ('0', '1'):
        output = run(ws, ['lean', 'Use.lean'], dict(ENV, PAPERLEAN_ACCELERATE='1', PAPERLEAN_EXACT=exact))
        assert output == plain, output


if sys.argv[1] == 'retained-metadata':
    retained_meta_symbols()
elif sys.argv[1] == 'metadata':
    metadata_aba()
    metadata_membership()
elif sys.argv[1] == 'cross-worktree':
    cross_worktree()
elif sys.argv[1] == 'unbound':
    unbound_inputs()
elif sys.argv[1] == 'aba':
    aba_case(False)
    aba_case(True)
elif sys.argv[1] in ('aba-single', 'aba-unit'):
    aba_case(sys.argv[1] == 'aba-unit')
elif sys.argv[1] == 'damage':
    damage()
elif sys.argv[1] == 'race':
    race_case(False)
    race_case(True)
elif sys.argv[1] == 'dependencies':
    dependency_damage()
elif sys.argv[1] == 'image':
    _, workspace = setup(ROOT / 'image')
    image_reporting(workspace)
else:
    raise SystemExit('expected aba, cross-worktree, unbound, damage, race, dependencies or image')
