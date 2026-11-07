#!/usr/bin/env python3
"""Kill a real build_artifact.py writer at controlled boundaries and race its real clear_cache."""
import argparse
from contextlib import contextmanager
import fcntl
import importlib.util
import json
import multiprocessing as mp
import os
from pathlib import Path
import signal
import subprocess
import sys

SHA = '1' * 40
sys.dont_write_bytecode = True


def load(source, cache):
    spec = importlib.util.spec_from_file_location('v023_artifact_candidate', source)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.ARTIFACT_CACHE = cache
    module.get_artifact_name = lambda: 'build-test'
    return module


def writer(source, cache, boundary, reached, release, invalid_payload=None):
    module = load(source, cache)

    def barrier(where):
        if boundary == where:
            reached.set()
            if not release.wait(20):
                raise RuntimeError('controlled writer barrier timed out: ' + where)

    def fake_backend(argv, **kwargs):
        if argv[:2] == ['gh', 'api']:
            data = '17 success\n' if 'head_sha=' in argv[2] else '23\n'
        elif argv[:3] == ['gh', 'run', 'download']:
            (Path(argv[argv.index('-D') + 1]) / 'fixture.tar.zst').write_bytes(b'fixture')
            data = ''
        elif argv[0] == 'tar':
            payload = Path(kwargs['cwd']) / 'lean-fixture'
            (payload / 'bin').mkdir(parents=True)
            for name in ['lean', 'lake', 'leanc']:
                path = payload / 'bin' / name
                path.write_text('#!/bin/sh\nexit 0\n')
                path.chmod(0o755)
            barrier('extraction')
            (payload / 'lib/lean/Extra').mkdir(parents=True)
            for name in ['Init.olean', 'Lean.olean', 'Lake.olean', 'Extra/M.olean']:
                (payload / 'lib/lean' / name).write_bytes(b'fixture module')
            (payload / 'bin' / 'lean-alias').symlink_to('lean')
            if invalid_payload:
                sentinel = cache.parent / 'sentinel'
                if invalid_payload == 'receipt-link':
                    (payload / module.CACHE_RECEIPT).symlink_to(sentinel)
                elif invalid_payload == 'receipt-hardlink':
                    os.link(sentinel, payload / module.CACHE_RECEIPT)
                elif invalid_payload == 'receipt-fifo':
                    os.mkfifo(payload / module.CACHE_RECEIPT)
                elif invalid_payload == 'external-link':
                    (payload / 'bin' / 'external').symlink_to(sentinel)
                else:
                    raise AssertionError(invalid_payload)
            data = ''
        else:
            raise AssertionError(f'unexpected backend invocation {argv}')
        return subprocess.CompletedProcess(argv, 0, data, '')

    module.subprocess.run = fake_backend
    original_replace = os.replace

    def at_publication(src, dst):
        if Path(dst) == module.get_cache_path(SHA):
            assert (Path(src) / module.CACHE_RECEIPT).is_file()
            barrier('publication')
        return original_replace(src, dst)

    module.os.replace = at_publication
    result = module.download_ci_artifact(SHA, quiet=True)
    # A racing clear may already have acquired the maintenance lock and deleted the publication.
    assert result == (None if invalid_payload else module.get_cache_path(SHA))


def verify_cache_miss(source, cache):
    assert not load(source, cache).is_cached(SHA)


def clearer(source, cache, contended, entered, saw_complete):
    module = load(source, cache)
    original_lock = module.cache_lock

    @contextmanager
    def observe(path, shared=False):
        if path == module.maintenance_lock_path() and not shared:
            # An actual nonblocking exclusive flock must conflict with the writer's shared lock.
            # This probe does not replace the blocking lock used by clear_cache below.
            with path.open('a') as handle:
                try:
                    fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                except BlockingIOError:
                    contended.set()
                else:
                    raise AssertionError('active writer did not hold its shared maintenance lock')
        with original_lock(path, shared):
            if path == module.maintenance_lock_path() and not shared:
                entered.set()
                assert module.is_cached(SHA), 'clear entered before complete publication'
                saw_complete.set()
            yield

    module.cache_lock = observe
    module.clear_cache()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source-root', type=Path, required=True)
    p.add_argument('--work', type=Path, required=True)
    a = p.parse_args()
    if not __debug__:
        raise SystemExit('run without Python -O')
    source = a.source_root.resolve() / 'script/build_artifact.py'
    work = a.work.resolve()
    work.mkdir(parents=True, exist_ok=True)
    if any(work.iterdir()):
        raise SystemExit('--work must be empty')
    ctx = mp.get_context('spawn')
    children, rows = [], []

    def launch(target, *args):
        proc = ctx.Process(target=target, args=args)
        proc.start()
        children.append(proc)
        return proc

    def joined(proc, expected=0):
        proc.join(20)
        assert proc.exitcode == expected, f'child exit {proc.exitcode}, expected {expected}'

    def retry(cache):
        reached, release = ctx.Event(), ctx.Event()
        proc = launch(writer, source, cache, 'none', reached, release)
        joined(proc)
        module = load(source, cache)
        assert module.is_cached(SHA)
        return module.get_cache_path(SHA)

    try:
        for boundary in ('extraction', 'publication'):
            cache = work / boundary
            module = load(source, cache)
            reached, release = ctx.Event(), ctx.Event()
            proc = launch(writer, source, cache, boundary, reached, release)
            assert reached.wait(15), f'writer did not reach {boundary}'
            assert not module.get_cache_path(SHA).exists() and not module.is_cached(SHA)
            os.kill(proc.pid, signal.SIGKILL)
            joined(proc, -signal.SIGKILL)
            assert not module.get_cache_path(SHA).exists() and not module.is_cached(SHA)
            dest = retry(cache)
            assert (dest / 'lib/lean/Extra/M.olean').read_bytes() == b'fixture module'
            rows.append({'case': 'killed-' + boundary, 'killed_exit': proc.exitcode,
                         'retry_complete': True})
        cache = work / 'clear-race'
        reached, release = ctx.Event(), ctx.Event()
        contended, entered, complete = ctx.Event(), ctx.Event(), ctx.Event()
        writing = launch(writer, source, cache, 'extraction', reached, release)
        assert reached.wait(15)
        clearing = launch(clearer, source, cache, contended, entered, complete)
        assert contended.wait(15), 'clear did not encounter the active writer lock'
        assert not entered.is_set()
        release.set()
        joined(writing)
        joined(clearing)
        assert entered.is_set() and complete.is_set() and not cache.exists()
        retry(cache)
        rows.append({'case': 'clear-racing-writer', 'exclusive_flock_conflicted': True,
                     'saw_complete_before_clear': True, 'retry_complete': True})
        sentinel = work / 'sentinel'
        sentinel.write_bytes(b'unrelated file')
        for kind in ('receipt-link', 'receipt-hardlink', 'receipt-fifo', 'external-link'):
            cache = work / kind
            joined(launch(writer, source, cache, 'none', None, None, kind))
            assert not load(source, cache).get_cache_path(SHA).exists()
            assert sentinel.read_bytes() == b'unrelated file'
            rows.append({'case': kind, 'rejected': True})
        cache = work / 'modified'
        dest = retry(cache)
        module_path = dest / 'lib/lean/Init.olean'
        times = module_path.stat()
        module_path.write_bytes(b'x' * times.st_size)
        os.utime(module_path, ns=(times.st_atime_ns, times.st_mtime_ns))
        joined(launch(verify_cache_miss, source, cache))
        (dest / load(source, cache).CACHE_RECEIPT).unlink()
        os.mkfifo(dest / load(source, cache).CACHE_RECEIPT)
        joined(launch(verify_cache_miss, source, cache))
        rows.append({'case': 'changed-file-and-unreadable-receipt', 'rejected': True})
    finally:
        for proc in children:
            if proc.is_alive():
                proc.kill()
                proc.join(5)
    (work / 'result.json').write_text(json.dumps({'status': 'passed', 'cases': rows}, indent=2) + '\n')


if __name__ == '__main__':
    main()
