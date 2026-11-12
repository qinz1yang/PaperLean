#!/usr/bin/env python3
"""Run a command in a new session and kill its whole process group on timeout.

Usage: run_with_timeout.py [--timeout SECONDS] -- COMMAND...
Exits with the command's exit status, or 124 if the command timed out.
"""
import argparse
import os
import signal
import subprocess
import sys


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--timeout", type=float, default=50.0)
    p.add_argument("command", nargs=argparse.REMAINDER)
    a = p.parse_args()
    command = a.command
    if command and command[0] == "--":
        command = command[1:]
    if not command:
        p.error("missing command")
    process = subprocess.Popen(command, stdin=subprocess.DEVNULL,
                               start_new_session=True)
    try:
        return process.wait(timeout=a.timeout)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()
        print(f"timed out after {a.timeout} seconds: {command}", file=sys.stderr)
        return 124


if __name__ == "__main__":
    sys.exit(main())
