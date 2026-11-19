#!/usr/bin/env python3
"""Time repeated runs of one residuum binary on one fixture.

Invoked only by `scripts/test_safe.py --benchmark`, inside the bounded worker,
so every run here inherits that cgroup's memory limit and the stage timeout.
Prints one JSON object: wall times per run, and a digest of the first run's
output so the caller can compare versions.
"""
import hashlib
import json
import subprocess
import sys
import time


def main():
    binary, command, fixture, repetitions, budget = sys.argv[1:]
    repetitions, budget = int(repetitions), float(budget)
    seconds, digest = [], None
    started = time.perf_counter()
    while len(seconds) < repetitions:
        before = time.perf_counter()
        run = subprocess.run([binary, command, fixture], capture_output=True)
        seconds.append(time.perf_counter() - before)
        if run.returncode != 0:
            sys.stderr.write(run.stderr.decode(errors='replace'))
            return run.returncode
        if digest is None:
            digest = hashlib.sha256(run.stdout).hexdigest()
        # Stop early rather than reach the stage timeout; record how many ran.
        if time.perf_counter() - started + seconds[-1] > budget:
            break
    print(json.dumps(dict(seconds=seconds, output_sha256=digest)))
    return 0


if __name__ == '__main__':
    sys.exit(main())
