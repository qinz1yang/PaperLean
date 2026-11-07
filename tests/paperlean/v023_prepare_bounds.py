"""Inspect actual analyzer queue/caching and extension admission with no timing thresholds."""
from pathlib import Path
import os
import re
import subprocess
import sys

work = Path(sys.argv[1]).resolve()
env = {k: v for k, v in os.environ.items() if not k.startswith(('PAPERLEAN_', 'LEAN_PATH'))}
env.update(LEAN_PATH=str(work), LEAN_NUM_THREADS='4')


def run(name, args, extra=None):
    p = subprocess.run(['lean', *args], cwd=work, env=env | (extra or {}), capture_output=True,
                       text=True, timeout=120)
    log = p.stdout + p.stderr
    (work / (name + '.log')).write_text(log)
    if p.returncode:
        raise RuntimeError(f'{name}: {p.returncode}\n{log}')
    return log


modules = {
    'LoadBound': 'initialize sharedValue : Nat ← pure 1\n' + ''.join(
        f'@[noinline] def v{i} : Nat := #[1,2,3][(sharedValue+{i})%3]!\n' for i in range(48)),
    'ImpureBound': 'unsafe def handleImpl : IO.Ref Nat := unsafeBaseIO (IO.mkRef 1)\n'
                   '@[implemented_by handleImpl] opaque handle : IO.Ref Nat\n',
    'ImpureInit': 'initialize y : Nat ← do return (← IO.monoMsNow) % 2\n'
                  'def readsTime : Nat := #[1,2][y]!\n'
}
for n, code in modules.items():
    (work / (n + '.lean')).write_text(code)
    run('build-' + n, ['-o', n + '.olean', n + '.lean'])
(work / 'Eval.lean').write_text('import Lean.PaperLean.NativeLibs\n'
    'def main (a : List String) : IO Unit :=\n'
    '  Lean.PaperLean.evalImpuritiesMain ⟨a[0]!⟩ ⟨a[1]!⟩ 30 8192\n')
(work / 'inputs').write_text(''.join(f'{n}\t{work}/{n}.olean\t0\n' for n in modules))
decisions = []
for width in (1, 4):
    events = work / ('events-' + str(width))
    run('eval-' + str(width), ['--run', 'Eval.lean', 'inputs', events.name],
        {'PAPERLEAN_EVAL_READERS': str(width), 'PAPERLEAN_EVAL_PROFILE': '1'})
    rows = [l.split('\t') for l in events.read_text().splitlines()]
    retained, frontier = map(int, next(r[1:] for r in rows if r[0] == 'readers'))
    hits, misses = map(int, next(r[1:] for r in rows if r[0] == 'initMemo'))
    assert retained == width < frontier, (width, retained, frontier)
    assert hits > 30 and misses > 0, (hits, misses)
    verdicts = [r for r in rows if r[0] in {'ok', 'impure', 'missing'}]
    assert {(r[0], Path(r[1]).stem) for r in verdicts} == {
        ('ok', 'LoadBound'), ('impure', 'ImpureBound'), ('impure', 'ImpureInit')}, verdicts
    decisions.append(verdicts)
assert decisions[0] == decisions[1]

# Explicitly request a persistent, extension-loaded import, where the three whitelisted pure
# folds qualify for speculation even without a prepared image. Check actual outputs across caps.
(work / 'ImportBudget.lean').write_text('import Lean\n'
    'example : True := True.intro\n'
    'unsafe def main : IO Unit := do\n'
    '  Lean.initSearchPath (← Lean.findSysroot)\n'
    '  Lean.enableInitializersExecution\n'
    '  let e ← Lean.importModules #[{module := `Lean}] {} (leakEnv := true) (loadExts := true)\n'
    '  unless e.contains ``Lean.Environment do throw <| IO.userError "missing declaration"\n'
    '  IO.println "imported"\n')
for cap in (0, 1, 8, 1000):
    text = run('import-' + str(cap), ['--run', 'ImportBudget.lean'],
               {'PAPERLEAN_IMPORT_THREADS': str(cap), 'PAPERLEAN_IMPORT_TIMING': '1'})
    assert 'imported' in text.splitlines()
    admits = [(int(a), int(b)) for a, b in re.findall(r'importWorker\.admitted [^\n]*active=(\d+) limit=(\d+)', text)]
    if cap:
        assert admits and all(0 < active <= bound == min(cap, 64) for active, bound in admits), (cap, admits)
    else:
        assert not admits and 'importWorker.budget ' in text, text
