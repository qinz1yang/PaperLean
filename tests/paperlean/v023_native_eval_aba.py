"""A stale or missing pack must not turn a process-local reference into a shared one."""
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import sys


work = Path(sys.argv[1]).resolve()
fixtures = Path(__file__).resolve().parent
live, other = work / 'live', work / 'replacement'
live.mkdir()
other.mkdir()
env = {k: v for k, v in os.environ.items() if not k.startswith(('PAPERLEAN_', 'DYLD_'))}
env.update(LEAN_PATH=str(live), LEAN_NUM_THREADS='2', LEAN_OLEAN_PACK='', LEAN_IMPORT_IMAGE='')
helper = fixtures / 'native_helper.lean'


def run(name, args, *, directory=work, extra=None):
    p = subprocess.run(args, cwd=directory, env=env | (extra or {}), text=True,
                       capture_output=True, timeout=120)
    log = p.stdout + p.stderr
    (work / (name + '.log')).write_text(log)
    if p.returncode:
        raise RuntimeError(f'{name} exited {p.returncode}\n{log}')
    return log


def identity(path):
    st = path.stat()
    return (st.st_dev, st.st_ino, st.st_mtime_ns, st.st_ctime_ns,
            hashlib.sha256(path.read_bytes()).hexdigest())


target = live / 'Probe.olean'
for root, module, source in [
    (live, 'Probe', 'unsafe def ctrImpl : IO.Ref Nat := unsafeBaseIO (IO.mkRef 0)\n'
     '@[implemented_by ctrImpl] opaque ctr : IO.Ref Nat\n'
     'def bump : IO Nat := do ctr.modify (· + 1); ctr.get\n'),
    (other, 'Probe', 'def harmless (n : Nat) := n\n'),
    (live, 'PureControl', 'def addOne (n : Nat) := n + 1\n')]:
    (root / (module + '.lean')).write_text(source)
    run(root.name + module, ['lean', '-o', module + '.olean', '-c', module + '.c', module + '.lean'],
        directory=root)
for name in ['Probe', 'PureControl']:
    run('link-' + name, ['leanc', '-shared', '-DLEAN_EXPORTING', '-o', work / (name + '.dylib'),
                         live / (name + '.c')])
run('interposer', ['cc', '-dynamiclib', fixtures / 'v023_native_eval_aba.c', '-o', 'swap.dylib'])
interpose = {'DYLD_INSERT_LIBRARIES': str(work / 'swap.dylib'), 'EVAL_ABA_TARGET': str(target),
             'EVAL_ABA_LIVE': str(live), 'EVAL_ABA_OTHER': str(other)}
(work / 'Pack.lean').write_text('import Lean.PaperLean.OLeanPack\n'
    'def main (a : List String) : IO Unit := do\n'
    '  let n ← Lean.PaperLean.OLeanPack.create #[⟨a[0]!⟩] ⟨a[1]!⟩\n'
    '  if n == 0 then throw (IO.userError "empty pack")\n')
(work / 'Eval.lean').write_text('import Lean.PaperLean.NativeLibs\n'
    'def main (a : List String) : IO Unit :=\n'
    '  Lean.PaperLean.evalImpuritiesMain ⟨a[0]!⟩ ⟨a[1]!⟩ 20 4096\n')
(work / 'UseProbe.lean').write_text('import Probe\n#eval bump\n#eval bump\n')
(work / 'UsePureControl.lean').write_text('import PureControl\n#eval addOne 41\n')
# Prove the syscall interposer works for this executable even if the repaired evaluator
# declines the loose input before opening it. Only the descriptor sees replacement bytes.
(work / 'Read.lean').write_text('import Init.System.IO\n'
    'def main (a : List String) : IO Unit := do\n'
    '  let b ← IO.FS.readBinFile ⟨a[0]!⟩\n'
    '  IO.FS.writeBinFile ⟨a[1]!⟩ b\n')
assert 'opened replacement' in run('calibration', ['lean', '--run', 'Read.lean', target, 'opened.bin'],
                                   extra=interpose)
assert (work / 'opened.bin').read_bytes() == (other / 'Probe.olean').read_bytes() != target.read_bytes()
run('older-pack', ['lean', '--run', 'Pack.lean', live, 'old.pack'])
# Content is identical, but the old pack binding no longer matches this module's inode.
shutil.copyfile(target, live / 'new.olean')
os.replace(live / 'new.olean', target)
run('reader-pack', ['lean', '--run', 'Pack.lean', live, 'reader.pack'])
expected = identity(target)
plain = run('plain', ['lean', 'UseProbe.lean']).strip().splitlines()
assert plain == ['1', '1'], plain


def check(label, name, pack, race):
    f = live / (name + '.olean')
    modules = work / (label + '.modules')
    modules.write_text(f'{name}\t{f}\t0\n')
    events = work / (label + '.events')
    inputs = {'LEAN_OLEAN_PACK': str(work / pack) if pack else ''}
    run(label, ['lean', '--run', 'Eval.lean', modules, events], extra=inputs | (interpose if race else {}))
    assert identity(target) == expected, label
    verdicts = events.read_text().splitlines()
    assert 'done' in verdicts, verdicts
    manifest = work / (label + '.manifest')
    run(label + '-manifest', ['lean', '--run', helper, 'manifest-events', events, manifest,
                             work / (name + '.dylib'), live, name])
    result = run(label + '-consumer', ['lean', 'Use' + name + '.lean'], extra={
        'LEAN_OLEAN_PACK': str(work / 'reader.pack'), 'PAPERLEAN_NATIVE_LIBS': str(manifest),
        'PAPERLEAN_IMPORT_TIMING': '1'})
    lines = [x for x in result.splitlines() if not x.startswith('paperlean-')]
    if name == 'PureControl':
        assert any(x.startswith(f'ok\t{f}\t') for x in verdicts), (label, verdicts)
        assert lines == ['42'] and 'native libs=1 modules=1 ' in result, (label, result)
    else:
        assert lines == plain and 'native libs=0 modules=0 ' in result, (label, lines, verdicts)
        assert not any(x.startswith(f'ok\t{f}\t') for x in verdicts), (label, verdicts)


check('positive', 'PureControl', 'reader.pack', False)
check('impure-control', 'Probe', 'reader.pack', False)
failures = []
for label, pack in [('loose-swap', None), ('stale-pack-swap', 'old.pack')]:
    try:
        check(label, 'Probe', pack, True)
    except AssertionError as e:
        failures.append(str(e))
if failures:
    raise AssertionError('\n'.join(failures))
