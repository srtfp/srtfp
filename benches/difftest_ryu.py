#!/usr/bin/env python3
"""Differential test: our verified Schubfach printer vs the Ryu oracle.

The shortest round-tripping decimal of a binary64 (with round-to-even tie
break) is UNIQUE, so two correct shortest printers must agree exactly. We
compare our verified Lean printer (`floatToStrRef`, the live v13 csimp) against
`std::to_chars` (libstdc++'s Ryu/Schubfach) over random finite binary64 values,
checking per input:

  1. round-trip:  float(ours) reproduces the input bits;
  2. value:       float(ours) and float(ryu) decode to the same double;
  3. shortest:    ours equals Python's repr (a verified shortest oracle).

NOTE: libstdc++ to_chars is not reliably minimal-digit for large integer-valued
doubles (it prints the full integer), so we do NOT require equal digit strings
vs Ryu, only equal decoded value; exact-shortest is checked against Python repr.

Build the two dumpers first:
    lake build diffDump
    g++ -O2 -std=c++20 -o benches/difftest_ryu benches/difftest_ryu.cpp

One-shot (finite, exits 0 when all agree -- the reproducible check):
    python3 benches/difftest_ryu.py [N]          # default N = 200000

Continuous soak (runs until interrupted, fresh seed per batch, periodic
reports; loud + logged on any divergence) -- for a background job:
    python3 benches/difftest_ryu.py --forever [--batch K]   # default K = 300000
"""
import argparse
import os
import random
import struct
import subprocess
import sys
import time
from datetime import datetime, timezone
from decimal import Decimal

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LEAN_DUMP = os.path.join(ROOT, ".lake", "build", "bin", "diffDump")
RYU_DUMP = os.path.join(HERE, "difftest_ryu")
FAIL_LOG = os.path.join(HERE, "difftest_failures.log")


def u2f(u: int) -> float:
    return struct.unpack("<d", struct.pack("<Q", u & 0xFFFFFFFFFFFFFFFF))[0]


def f2u(x: float) -> int:
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def gen_finite(n: int, rng: random.Random) -> list[int]:
    """n random finite binary64 bit patterns (subnormals + zeros allowed,
    NaN/Inf excluded), prefixed with a deterministic edge-case set."""
    edges = [
        0, 1 << 63,                       # +0, -0
        1, (1 << 63) | 1,                 # min subnormal +/-
        0x7FEFFFFFFFFFFFFF,               # max finite
        0x000FFFFFFFFFFFFF,               # max subnormal
        0x0010000000000000,               # min normal
        f2u(1.0), f2u(0.1), f2u(2.5), f2u(1e308), f2u(5e-324),
    ]
    out = list(edges)
    while len(out) < n:
        u = rng.getrandbits(64)
        if (u >> 52) & 0x7FF == 0x7FF:    # NaN / Inf
            continue
        out.append(u)
    return out[:n]


def canon(s: str):
    """(sign, digit-tuple, exponent), trailing zeros stripped; None if bad."""
    try:
        return Decimal(s).normalize().as_tuple()
    except Exception:
        return None


def run_dump(cmd: list[str], inputs: list[int]) -> dict[int, str]:
    payload = "\n".join(str(u) for u in inputs) + "\n"
    res = subprocess.run(cmd, input=payload, capture_output=True, text=True,
                         check=True, cwd=ROOT)
    out = {}
    for line in res.stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        bits_str, _, val = line.partition(" ")
        out[int(bits_str)] = val
    return out


def compare(inputs: list[int]):
    """Returns (checked, mismatches, nonshortest, ryu_nonminimal).
    `mismatches` = value/round-trip divergence vs Ryu (real bugs);
    `nonshortest` = ours differs from Python's verified-shortest repr."""
    ours = run_dump([LEAN_DUMP], inputs)
    ryu = run_dump([RYU_DUMP], inputs)
    mismatches, nonshortest, ryu_nonminimal, checked = [], [], 0, 0
    for u in inputs:
        o, r = ours.get(u), ryu.get(u)
        if o is None or r is None:
            mismatches.append((u, o, r, "missing output"))
            continue
        checked += 1
        try:
            fo, fr = float(o), float(r)
        except Exception:
            mismatches.append((u, o, r, "unparseable output"))
            continue
        if f2u(fo) != u:
            mismatches.append((u, o, r, "ours does not round-trip"))
        elif f2u(fr) != f2u(fo):
            mismatches.append((u, o, r, "value disagrees with Ryu"))
        py = repr(u2f(u))
        if canon(o) != canon(py):
            nonshortest.append((u, o, py))
        if canon(r) != canon(py):
            ryu_nonminimal += 1
    return checked, mismatches, nonshortest, ryu_nonminimal


def require_dumpers():
    for tool in (LEAN_DUMP, RYU_DUMP):
        if not os.path.exists(tool):
            sys.exit(f"missing {tool}; build the helpers first with: make")


def now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def log_failures(batch_seed, mismatches, nonshortest):
    with open(FAIL_LOG, "a") as f:
        f.write(f"\n=== {now()} batch_seed={hex(batch_seed)} ===\n")
        for u, o, r, why in mismatches:
            f.write(f"  VALUE  bits={u} ({u2f(u)!r}) ours={o!r} ryu={r!r} [{why}]\n")
        for u, o, py in nonshortest:
            f.write(f"  SHORT  bits={u} ({u2f(u)!r}) ours={o!r} python={py!r}\n")


def one_shot(n: int, seed: int) -> int:
    print(f"differential test: {n} finite binary64, seed {hex(seed)}", flush=True)
    inputs = gen_finite(n, random.Random(seed))
    checked, mismatches, nonshortest, ryu_nm = compare(inputs)
    for u, o, r, why in mismatches[:20]:
        print(f"  FAIL value bits={u} ({u2f(u)!r}) ours={o!r} ryu={r!r} [{why}]")
    for u, o, py in nonshortest[:20]:
        print(f"  FAIL short bits={u} ({u2f(u)!r}) ours={o!r} python={py!r}")
    ok = not mismatches and not nonshortest
    print(f"\n{checked} finite values checked.")
    print(f"  vs Ryu (std::to_chars): value/round-trip agreement = "
          f"{'ALL' if not mismatches else f'{checked-len(mismatches)}/{checked}'}")
    print(f"  vs Python repr (shortest): exact shortest = "
          f"{'ALL' if not nonshortest else f'{checked-len(nonshortest)}/{checked}'}")
    print(f"  (informational) to_chars non-minimal-digit on {ryu_nm} large-integer "
          f"cases; ours is minimal there")
    return 0 if ok else 1


def forever(batch: int, seed: int) -> int:
    print(f"differential soak: forever, batch={batch}, base seed {hex(seed)}", flush=True)
    print(f"  divergences (if any) appended to {FAIL_LOG}", flush=True)
    total = total_fail = total_short = total_nm = 0
    t0 = time.time()
    i = 0
    try:
        while True:
            batch_seed = (seed + i * 0x9E3779B97F4A7C15) & ((1 << 64) - 1)
            inputs = gen_finite(batch, random.Random(batch_seed))
            checked, mismatches, nonshortest, ryu_nm = compare(inputs)
            total += checked
            total_fail += len(mismatches)
            total_short += len(nonshortest)
            total_nm += ryu_nm
            i += 1
            if mismatches or nonshortest:
                log_failures(batch_seed, mismatches, nonshortest)
                print(f"!! {now()} DIVERGENCE in batch {i} (seed {hex(batch_seed)}): "
                      f"{len(mismatches)} value, {len(nonshortest)} shortest -> {FAIL_LOG}",
                      flush=True)
                for u, o, r, why in mismatches[:5]:
                    print(f"     bits={u} ({u2f(u)!r}) ours={o!r} ryu={r!r} [{why}]", flush=True)
            rate = total / max(time.time() - t0, 1e-9) / 1e6
            print(f"[{now()}] batches={i} tested={total/1e6:.2f}M "
                  f"divergences={total_fail + total_short} "
                  f"rate={rate:.2f}M/s (to_chars-nonminimal={total_nm}, ours minimal)",
                  flush=True)
    except KeyboardInterrupt:
        pass
    print(f"\nstopped: {total} values over {i} batches, "
          f"{total_fail} value + {total_short} shortest divergences.", flush=True)
    return 1 if (total_fail or total_short) else 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("n", nargs="?", type=int, default=200000,
                    help="one-shot sample size (default 200000)")
    ap.add_argument("--forever", action="store_true",
                    help="run continuously with a fresh seed per batch")
    ap.add_argument("--batch", type=int, default=300000,
                    help="samples per batch in --forever mode (~4s; default 300000)")
    ap.add_argument("--seed", type=lambda x: int(x, 0), default=0xD1FFC0DE)
    args = ap.parse_args()
    require_dumpers()
    sys.exit(forever(args.batch, args.seed) if args.forever
             else one_shot(args.n, args.seed))


if __name__ == "__main__":
    main()
