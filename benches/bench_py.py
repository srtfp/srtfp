#!/usr/bin/env python3
"""Reference Python float->str bench (CPython `repr`).

Usage: bench_py.py <adversarial|nice|uniform> [--checksum]

Inputs come from benches/corpora/<corpus>.u64, written by `lake exe
genCorpora`, guaranteeing bit-identical inputs across the harnesses.
"""
import os
import struct
import sys
import time

def load(label):
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "corpora", f"{label}.u64")
    with open(path) as f:
        return [struct.unpack("<d", struct.pack("<Q", int(line)))[0] for line in f if line.strip()]

label = sys.argv[1] if len(sys.argv) > 1 else "adversarial"
if label not in ("nice", "uniform"):
    label = "adversarial"
xs = load(label)

if "--checksum" in sys.argv[2:]:
    s = 0
    for f in xs:
        s = (s + struct.unpack("<Q", struct.pack("<d", f))[0]) & 0xFFFFFFFFFFFFFFFF
    print(f"{label}: n={len(xs)} sum_bits={s}")
    sys.exit(0)

N, M = 1000, 5
for _ in range(50):
    for f in xs:
        repr(f)

times = []
for _ in range(M):
    sink = 0
    t0 = time.perf_counter_ns()
    for _ in range(N):
        for f in xs:
            sink ^= len(repr(f))
    t1 = time.perf_counter_ns()
    times.append((t1 - t0) // (N * len(xs)))
    if sink == 12345:
        print()

times.sort()
print(f"python/{label}: median = {times[M // 2]} ns/call (runs: {times})")
