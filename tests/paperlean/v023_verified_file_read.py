# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Interpose a FIFO between receipt observation and the verified open. Never open a pipe writer."""
from pathlib import Path
import os
import subprocess
import sys
import time

Path('subject').write_bytes(b'verified bytes\n')
Path('empty').touch()
Path('cache').mkdir()
Path('cache/owned').write_bytes(b'verified bytes\n')
with subprocess.Popen([sys.argv[1]], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True) as child:
    try:
        for _ in range(500):
            if Path('ready').exists():
                break
            assert child.poll() is None, child.stdout.read()
            time.sleep(0.02)
        else:
            raise AssertionError('timed out waiting for the regular-read control')
        Path('subject').rename('original')
        os.mkfifo('subject')
        Path('cache').rename('original-cache')
        Path('cache').mkdir()
        Path('cache/owned').symlink_to('../original-cache/owned')
        Path('replaced').touch()
        output, _ = child.communicate(timeout=10)
        assert child.returncode == 0 and 'substituted FIFO rejected' in output, output
        print(output, end='')
    finally:
        if child.poll() is None:
            child.kill()
            child.wait()
