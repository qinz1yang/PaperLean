#!/usr/bin/env python3
"""Exercise lean_profile.sh cleanup with a real unrelated loopback listener and owned load PID."""
import argparse
import json
import os
from pathlib import Path
import signal
import socket
import subprocess
import sys
import time


def wait_file(path, proc, timeout=10):
    deadline = time.monotonic() + timeout
    while not path.exists() or not path.stat().st_size:
        if proc.poll() is not None or time.monotonic() >= deadline:
            raise RuntimeError(f'{path} unavailable; child exit={proc.poll()}')
        time.sleep(0.02)


def executable(path, text):
    path.write_text(text)
    path.chmod(0o755)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source-root', type=Path, required=True)
    p.add_argument('--work', type=Path, required=True)
    a = p.parse_args()
    if not __debug__:
        raise SystemExit('run without Python -O')
    script = a.source_root.resolve() / 'script/lean_profile.sh'
    work = a.work.resolve()
    work.mkdir(parents=True, exist_ok=True)
    if any(work.iterdir()):
        raise SystemExit('--work must be empty')
    fake = work / 'bin'
    fake.mkdir()
    # Keep the script's transient profile directory inside the fixture's own work area.
    executable(fake / 'mktemp', f'#!{sys.executable}\n' + '''import os, sys, tempfile
from pathlib import Path
assert sys.argv[1:] == ['-d', '/tmp/lean-profile-XXXXXX']
case = Path(os.environ['CASE'])
path = tempfile.mkdtemp(prefix='lean-profile-', dir=case)
(case / 'tempdir').write_text(path)
print(path)
''')
    executable(fake / 'samply', f'#!{sys.executable}\n' + '''import os, signal, sys
from pathlib import Path
case = Path(os.environ['CASE'])
if sys.argv[1] == 'record':
    Path(sys.argv[sys.argv.index('-o') + 1]).write_bytes(b'fixture')
    sys.exit(0)
assert sys.argv[1] == 'load'
def stop(sig, frame):
    (case / 'terminated').write_text(str(sig))
    sys.exit(0)
signal.signal(signal.SIGTERM, stop)
(case / 'owned.pid').write_text(str(os.getpid()))
if os.environ['MODE'] == 'normal':
    print('Local server listening ' + 'a' * 32, flush=True)
# During INT/TERM tests the real script remains in its bounded readiness loop.
while True: signal.pause()
''')
    executable(fake / 'python3', f'#!{sys.executable}\n' + '''import os, sys
from pathlib import Path
case = Path(os.environ['CASE'])
if Path(sys.argv[1]).name == 'symbolicate_profile.py':
    Path(sys.argv[sys.argv.index('-o') + 1]).write_bytes(b'fixture-demangled')
elif Path(sys.argv[1]).name == 'serve_profile.py':
    assert Path(sys.argv[2]).read_bytes() == b'fixture-demangled'
    (case / 'served').touch()
else:
    raise AssertionError(sys.argv)
''')
    # The removed port-wide fallback would target this fixture-owned unrelated listener.
    executable(fake / 'lsof', '#!/usr/bin/env bash\ntouch "$CASE/lsof-called"\necho "$LISTENER_PID"\n')
    listener_code = '''import socket, sys
from pathlib import Path
with socket.socket() as server:
    server.bind(('127.0.0.1', 0)); server.listen()
    Path(sys.argv[1]).write_text(str(server.getsockname()[1]))
    while True:
        conn, _ = server.accept()
        with conn: conn.sendall(b'alive\\n')
'''
    port_file = work / 'listener-port'
    with (work / 'listener.log').open('wb') as log:
        listener = subprocess.Popen([sys.executable, '-c', listener_code, str(port_file)],
                                    stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
    rows = []
    try:
        try:
            wait_file(port_file, listener)
        except RuntimeError as e:
            raise SystemExit(f'real 127.0.0.1 ephemeral listener required; see {work / "listener.log"}: {e}')
        port = int(port_file.read_text())
        for mode, sig, expected in [('normal', None, 0), ('term', signal.SIGTERM, 143), ('int', signal.SIGINT, 130)]:
            case = work / mode
            case.mkdir()
            env = dict(os.environ, PATH=str(fake) + os.pathsep + os.environ['PATH'], CASE=str(case), MODE=mode,
                       SAMPLY_PORT=str(port), LISTENER_PID=str(listener.pid), PROFILE_KEEP='0')
            with (case / 'driver.log').open('wb') as log:
                proc = subprocess.Popen(['bash', str(script), 'fixture'], cwd=case, env=env,
                                        stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
            owned = None
            try:
                if sig:
                    wait_file(case / 'owned.pid', proc)
                    owned = int((case / 'owned.pid').read_text())
                    assert os.getpgid(owned) == proc.pid
                    proc.send_signal(sig)
                status = proc.wait(timeout=12)
                assert status == expected, f'{mode}: exit {status}, expected {expected}'
                owned = int((case / 'owned.pid').read_text())
                assert (case / 'terminated').read_text() == str(signal.SIGTERM.value)
                assert (case / 'served').exists() == (mode == 'normal')
                assert not (case / 'lsof-called').exists()
                assert not Path((case / 'tempdir').read_text()).exists()
                # SIGTERM receipt plus PID disappearance verifies both termination and reaping.
                try:
                    os.kill(owned, 0)
                except ProcessLookupError:
                    pass
                else:
                    raise AssertionError(f'owned load child {owned} still exists after {mode}')
                assert listener.poll() is None
                with socket.create_connection(('127.0.0.1', port), timeout=2) as client:
                    with client.makefile('rb') as stream:
                        assert stream.readline() == b'alive\n'
                rows.append({'case': mode, 'exit': status, 'owned_pid': owned, 'listener_pid': listener.pid,
                             'listener_connected_after_cleanup': True})
            finally:
                # Stop only this test invocation's private process group after a failure/timeout.
                # The unrelated listener has its own session and is disposed below.
                live = proc.poll() is None
                if owned is None and (case / 'owned.pid').is_file():
                    value = (case / 'owned.pid').read_text().strip()
                    owned = int(value) if value.isdigit() else None
                if owned is not None:
                    try:
                        live = live or os.getpgid(owned) == proc.pid
                    except ProcessLookupError:
                        pass
                if live:
                    try:
                        os.killpg(proc.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                proc.wait()
    finally:
        if listener.poll() is None:
            listener.terminate()
        listener.wait(timeout=5)
    (work / 'result.json').write_text(json.dumps({'status': 'passed', 'cases': rows}, indent=2) + '\n')


if __name__ == '__main__':
    main()
