"""Actual subprocess used by OutputCancel.lean."""
import os
import select
import signal
import sys

mode, fifo = sys.argv[1:]
if mode == "closed":
    for stream in (0, 1, 2):
        os.close(stream)
elif mode == "blocked":
    # Keep both output pipes open. Wait for the writer to start, then leave its
    # 2 MiB of input unread so it cannot finish before cancellation.
    os.write(1, b"stdout")
    os.write(2, b"stderr")
    select.select([0], [], [])
else:
    raise ValueError(mode)

with open(fifo, "w") as f:
    print(os.getpid(), file=f)
while True:
    signal.pause()
