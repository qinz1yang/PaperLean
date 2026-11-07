#!/usr/bin/env python3
"""Exercise the real Radar entry point with local drivers. No network or compiler is used."""
import argparse
import fcntl
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time


def executable(path, text):
    path.write_text(text)
    path.chmod(0o755)


def wait_file(path, timeout=10):
    deadline = time.monotonic() + timeout
    while not path.exists():
        if time.monotonic() >= deadline:
            raise RuntimeError(f"timed out waiting for {path}")
        time.sleep(0.02)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--work', type=Path, required=True)
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit('run without Python -O')
    script = args.source_root.resolve() / 'tests/bench_other.sh'
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=True)
    if any(work.iterdir()):
        raise SystemExit('--work must be empty')
    fake = work / 'bin'
    fake.mkdir()
    shell = '#!/usr/bin/env bash\nset -eu\n'
    executable(fake / 'nproc', shell + 'echo 1\n')
    executable(fake / 'cmake', shell + 'echo configure >> "$LOG"\nmkdir -p stage1\n')
    executable(fake / 'make', shell + 'echo make >> "$LOG"\nprintf "%s\\n" "$TAG" > tests/part2.measurements.jsonl\n')
    executable(fake / 'python3', shell + 'touch "$ENTERED"\nexec "$REAL_PYTHON" "$@"\n')
    executable(fake / 'curl', f'#!{sys.executable}\n' + '''import os, sys, time
from pathlib import Path
argv = sys.argv[1:]
assert '--fail' in argv and '--location' in argv
output = Path(argv[argv.index('-o') + 1])
with open(os.environ['CURL_LOG'], 'a') as log: log.write(os.environ['TAG'] + '\\n')
if os.environ.get('GATE'):
    gate = Path(os.environ['GATE']); gate.with_suffix('.started').touch()
    deadline = time.monotonic() + 15
    while not gate.exists():
        if time.monotonic() >= deadline: sys.exit(70)
        time.sleep(0.02)
mode = os.environ['MODE']
output.write_bytes({'empty': b'', 'fail': b'incomplete', 'ok': os.environ['TAG'].encode()}[mode])
sys.exit(22 if mode == 'fail' else 0)
''')
    jobs = []
    results = []

    def start(tag, cache, mode, gate=None):
        case = work / tag
        (case / 'script').mkdir(parents=True)
        (case / 'tests').mkdir()
        (case / 'previous').write_text('old-result\n')
        (case / 'tests/part2.measurements.jsonl').write_text('stale-aggregate\n')
        executable(case / 'script/prepare-llvm-linux.sh', shell + 'echo prepare >> "$LOG"\n')
        env = dict(os.environ, PATH=f'{fake}{os.pathsep}' + os.environ['PATH'], REAL_PYTHON=sys.executable,
                   RADAR_CACHE=str(cache), RADAR_OUT=str(case / 'previous'), TAG=tag, MODE=mode,
                   LOG=str(case / 'stages'), CURL_LOG=str(work / 'curl-calls'),
                   ENTERED=str(case / 'entered'), GATE=str(gate) if gate else '')
        with (case / 'driver.log').open('wb') as log:
            proc = subprocess.Popen(['bash', str(script)], cwd=case, env=env, stdout=log,
                                    stderr=subprocess.STDOUT, start_new_session=True)
        jobs.append(proc)
        return proc, case

    def finish(job, success):
        proc, case = job
        rc = proc.wait(timeout=20)
        if rc < 0 or (rc == 0) != success:
            raise AssertionError(f'{case.name}: unexpected exit {rc}')
        assert (case / 'previous').read_text() == (case.name + '\n' if success else 'old-result\n')
        assert (case / 'stages').exists() == success
        results.append({'case': case.name, 'exit': rc})

    def archive(cache):
        return cache / 'llvm/23.1.0.tar.zst'

    try:
        cache = work / 'cache'
        for tag, mode in [('empty-200', 'empty'), ('failed-download', 'fail')]:
            finish(start(tag, cache, mode), False)
            assert not archive(cache).exists()
            assert not list(archive(cache).parent.glob('*.tmp-*'))
        archive(cache).touch()
        finish(start('failed-empty-recovery', cache, 'fail'), False)
        assert archive(cache).stat().st_size == 0
        finish(start('repair-empty', cache, 'ok'), True)
        assert archive(cache).read_bytes() == b'repair-empty'
        stamp = archive(cache).stat()
        finish(start('reuse-winner', cache, 'fail'), True)
        assert archive(cache).stat().st_ino == stamp.st_ino and archive(cache).stat().st_ctime_ns == stamp.st_ctime_ns
        assert 'reuse-winner' not in (work / 'curl-calls').read_text().splitlines()
        concurrent = work / 'concurrent-cache'
        gate = work / 'release'
        first = start('first', concurrent, 'ok', gate)
        wait_file(gate.with_suffix('.started'))
        with Path(str(archive(concurrent)) + '.lock').open('a') as lock:
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                pass
            else:
                raise AssertionError('active transfer did not hold the archive publication lock')
        second = start('second', concurrent, 'fail')
        wait_file(second[1] / 'entered')
        gate.touch()
        finish(first, True)
        finish(second, True)
        assert archive(concurrent).read_bytes() == b'first'
        assert 'second' not in (work / 'curl-calls').read_text().splitlines()
        # A completed entry already present when our private transfer ends must survive.
        other_cache = work / 'winner-cache'
        gate = work / 'external-release'
        job = start('late-download', other_cache, 'ok', gate)
        wait_file(gate.with_suffix('.started'))
        winner = archive(other_cache).with_suffix('.winner')
        winner.write_bytes(b'already complete')
        winner.replace(archive(other_cache))
        stamp = archive(other_cache).stat()
        gate.touch()
        finish(job, True)
        assert archive(other_cache).read_bytes() == b'already complete'
        assert archive(other_cache).stat().st_ino == stamp.st_ino
    finally:
        for proc in jobs:
            if proc.poll() is None:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
    (work / 'result.json').write_text(json.dumps({'status': 'passed', 'cases': results}, indent=2) + '\n')


if __name__ == '__main__':
    main()
