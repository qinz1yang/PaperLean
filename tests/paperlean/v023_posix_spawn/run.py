#!/usr/bin/env python3
"""Build and run the POSIX spawn probes with the selected runtime in an empty directory."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import shlex
import subprocess


def compiler_command(explicit, variable, fallback):
    # Explicit CLI choices remain one executable; CTest's CXX includes flags.
    if explicit is not None:
        return [explicit]
    return shlex.split(os.environ.get(variable) or fallback)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean', type=Path, required=True)
    p.add_argument('--leanc', type=Path, required=True)
    p.add_argument('--work', type=Path, required=True)
    p.add_argument('--cc')
    p.add_argument('--cxx')
    a = p.parse_args()
    try:
        cc = compiler_command(a.cc, 'CC', 'cc')
        cxx = compiler_command(a.cxx, 'CXX', 'c++')
    except ValueError as ex:
        p.error(f'invalid compiler command: {ex}')
    if not cc or not cxx:
        p.error('CC and CXX must specify a compiler')
    system = platform.system()
    if system not in ('Darwin', 'Linux'):
        p.error('this probe targets Darwin and Linux')
    src = Path(__file__).resolve().parent
    work = a.work.resolve()
    work.mkdir(parents=True, exist_ok=True)
    if any(work.iterdir()): p.error('--work must be empty')
    lean, leanc = a.lean.resolve(), a.leanc.resolve()
    env = {k: v for k, v in os.environ.items() if not k.startswith(('PAPERLEAN_', 'ELAN_', 'LEAN_'))}
    env.update(U06_PARENT='inherited', U06_DROP='present')
    events = []

    def run(name, argv, extra=None):
        argv = list(map(str, argv))
        cp = subprocess.run(argv, cwd=work, stdin=subprocess.DEVNULL, capture_output=True,
                            timeout=90, env=dict(env, **(extra or {})))
        (work / (name + '.out')).write_bytes(cp.stdout)
        (work / (name + '.err')).write_bytes(cp.stderr)
        events.append(dict(name=name, argv=argv, exit=cp.returncode))
        (work / 'commands.json').write_text(json.dumps(events, indent=2) + '\n')
        if cp.returncode: raise SystemExit(f'{name}: exit {cp.returncode}; inspect {work}')
        return cp

    prefix = Path(run('prefix', [lean, '--print-prefix']).stdout.decode().strip())
    run('reporter', [*cc, '-O2', src / 'report.c', '-o', work / 'reporter'])
    run('fixture', [*cxx, '-std=c++17', '-I' + str(prefix / 'include'), '-c', src / 'fixture.cpp',
                    '-o', work / 'fixture.o'])
    run('lean-main', [lean, '--root=' + str(src), '-c', work / 'main.c', src / 'SpawnCase.lean'])
    run('compile-main', [leanc, '-c', work / 'main.c', '-o', work / 'main.o'])
    driver = work / 'driver'
    # Link with the selected toolchain so its bundled dependencies are found.
    run('link', [leanc, '-o', driver, work / 'main.o', work / 'fixture.o'])
    fault = work / ('fault.dylib' if system == 'Darwin' else 'fault.so')
    flags = ['-dynamiclib'] if system == 'Darwin' else ['-shared']
    run('interposer', [*cc, *flags, '-fPIC', src / 'dup_fault.c', '-o', fault,
                       *([] if system == 'Darwin' else ['-ldl'])])
    cwd = work / 'child'
    bad, good = cwd / 'bad', cwd / 'good'
    bad.mkdir(parents=True)
    good.mkdir()
    for name in ('u06-helper', 'denied', 'plain'):
        x = bad / name
        x.write_text('exit 77\n'); x.chmod(0o644)
    shutil.copy2(work / 'reporter', good / 'u06-helper')
    shutil.copy2(work / 'reporter', cwd / 'u06-helper')
    plain = good / 'plain'
    plain.write_text('printf \'%s:%s\\n\' "$1" "$U06_JOIN"\n')
    plain.chmod(0o755)

    # stdin is /dev/null, stdout and stderr are pipes in the parent. A mask bit closes
    # the corresponding descriptor after runtime initialization. The external reporter
    # classifies descriptors before opening its output file.
    cases = [(0, 'NNN', 'u06-helper', 'bad:absent:good', False),
             (7, 'PPP', 'u06-helper', 'bad:absent:good', True),
             (1, 'INN', 'u06-helper', '', False),
             (7, 'NNN', 'u06-helper', 'bad::absent', True),
             (3, 'NIP', './good/u06-helper', 'absent', False),
             (7, 'III', 'u06-helper', 'good:', True)]
    for i, (mask, modes, cmd, path, inherit) in enumerate(cases):
        report = work / f'streams-{i}.report'
        run(f'streams-{i}', [driver, 'streams', cmd, cwd, report, mask, *modes, path, int(inherit)])
        kinds = ''.join((('C' if mask & (1 << j) else 'NPP'[j]) if m == 'I' else m)
                        for j, m in enumerate(modes))
        expected = f'{kinds} 0 1 last {"inherited" if inherit else "missing"} removed\n'
        actual = report.read_text()
        if actual != expected: raise SystemExit(f'streams-{i}: expected {expected!r}, got {actual!r}')
    reference = subprocess.run([work / 'reporter', '--execvp-reference', 'plain', 'two words'],
                               cwd=cwd, env={'PATH': 'bad:good', 'U06_JOIN': 'last'},
                               capture_output=True, timeout=15)
    if (reference.returncode, reference.stdout) not in [(0, b'two words:last\n'), (255, b'')]:
        raise SystemExit(f'unexpected libc execvp result: {reference!r}')
    run('lookup', [driver, 'lookup', cwd, 'yes' if reference.returncode == 0 else 'no'])
    cp = run('failure', [driver, 'failure', cwd])
    if cp.stdout != b'u06-parent-buffer': raise SystemExit(f'buffer duplication: {cp.stdout!r}')
    diagnostic = b'could not redirect child standard stream\n'
    preload = 'DYLD_INSERT_LIBRARIES' if system == 'Darwin' else 'LD_PRELOAD'
    cp = run('open-failure', [driver, 'open-failure'], {preload: str(fault)})
    if diagnostic not in cp.stderr: raise SystemExit('missing injected open failure diagnostic')
    cp = run('dup-failure', [driver, 'dup-failure'], {preload: str(fault)})
    if diagnostic not in cp.stderr: raise SystemExit('missing injected dup2 failure diagnostic')
    receipt = {'result': 'passed', 'platform': platform.platform(), 'lean': str(lean),
               'driver_sha256': hashlib.sha256(driver.read_bytes()).hexdigest(), 'cases': len(cases) + 4}
    (work / 'result.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt))


if __name__ == '__main__':
    main()
