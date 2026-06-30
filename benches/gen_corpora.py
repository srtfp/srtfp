#!/usr/bin/env python3
"""Float-to-String benchmark corpus generator.

Single source of truth for the three corpora used by:
  - BenchFloatToString.lean        (via benches/corpora.lean)
  - benches/bench_ref.cpp          (via benches/corpora.h + corpora.cpp)
  - benches/bench_py.py            (imports this module directly)
  - benches/bench_java/Bench.java  (via benches/bench_java/Corpora.java)

We serialise each float as its 64-bit IEEE-754 bit pattern (u64). Each
impl reconstructs the float via Float.ofBits / std::bit_cast<double> /
struct.unpack. This guarantees bit-identical inputs regardless of
decimal-parsing differences across languages.

Run:
    python3 benches/gen_corpora.py             # fresh random seed
    python3 benches/gen_corpora.py --seed 0xN  # reproduce a past corpus

Re-emits benches/corpora.lean, benches/corpora.h, benches/corpora.cpp.
The emitted files are committed; users don't need to run the generator.
"""

import math
import os
import random
import secrets
import struct
import sys

# A fresh seed is drawn on every regeneration (so the random corpora can't
# be overfit), then recorded in corpora/SEED.txt so that importers
# (bench_py.py) see the same corpus as the committed emits, and any past
# corpus is reproducible via --seed.
_SEED_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                          "corpora", "SEED.txt")

def _load_seed() -> int:
    try:
        with open(_SEED_FILE) as f:
            return int(f.read().strip(), 0)
    except (OSError, ValueError):
        return 0xDEADBEEF  # corpora predating SEED.txt

SEED = _load_seed()

# ---------------------------------------------------------------------------
# Float <-> u64 bit helpers
# ---------------------------------------------------------------------------

def f2u(x: float) -> int:
    return struct.unpack("<Q", struct.pack("<d", x))[0]

def u2f(u: int) -> float:
    return struct.unpack("<d", struct.pack("<Q", u & 0xFFFFFFFFFFFFFFFF))[0]

def is_finite_u64(u: int) -> bool:
    exp = (u >> 52) & 0x7FF
    return exp != 0x7FF  # NaN and infinity both have exp = 0x7FF


# ---------------------------------------------------------------------------
# Corpus: adversarial
# ---------------------------------------------------------------------------
# Superset of the Ryu/Schubfach test corpus (every finite value of every
# case group in Tests/Ryu.lean, exported bit-exactly via a one-off
# `lake env lean --run` script printing `Float.toBits` over the Case
# arrays), plus the original hand-picked set, power-of-two ulp
# neighbourhoods and the 0.1 + 0.2 family.

# Every finite value from Tests/Ryu.lean (d2s* + f2s* + d2sExactTies).
RYU_SUITE_BITS = [
    0x0000000000000000, 0x8000000000000000, 0x3FF0000000000000, 0xBFF0000000000000,
    0x0010000000000000, 0x7FEFFFFFFFFFFFFF, 0x0000000000000001, 0x3E60000000000000,
    0xC352BD2668E077C4, 0x00000000000F4240, 0x00000000016E3600, 0x0000008CDCDEA440,
    0x434018601510C000, 0x43D055DC36F24000, 0x43E052961C6F8000, 0x3FF3C0CA2A5B1D5D,
    0x4830F0CF064DD592, 0x4840F0CF064DD592, 0x4850F0CF064DD592, 0x3FF3333333333333,
    0x3FF3AE147AE147AE, 0x3FF3BE76C8B43958, 0x3FF3C083126E978D, 0x3FF3C0C1FC8F3238,
    0x3FF3C0C9539B8887, 0x3FF3C0CA4283DE1B, 0x3FF3C0CA43DB770A, 0x3FF3C0CA428ABD53,
    0x3FF3C0CA428C1D2B, 0x3FF3C0CA428C51F2, 0x3FF3C0CA428C58FC, 0x3FF3C0CA428C59DD,
    0x3FF3C0CA428C59F8, 0x3FF3C0CA428C59FB, 0x40112E0BE8047A7D, 0x40112E0BE815A889,
    0x40112E0BE826D695, 0x40112E0BE83804A1, 0x40112E0BE84932AD, 0x0040000000000000,
    0x007FFFFFFFFFFFFF, 0x0290000000000000, 0x029FFFFFFFFFFFFF, 0x4350000000000000,
    0x435FFFFFFFFFFFFF, 0x1330000000000000, 0x133FFFFFFFFFFFFF, 0x3A6FA7161A4D6E0C,
    0x433FFFFFFFFFFFFF, 0x4340000000000000, 0x4024000000000000, 0x4059000000000000,
    0x408F400000000000, 0x40C3880000000000, 0x40F86A0000000000, 0x412E848000000000,
    0x416312D000000000, 0x4197D78400000000, 0x41CDCD6500000000, 0x4202A05F20000000,
    0x42374876E8000000, 0x426D1A94A2000000, 0x42A2309CE5400000, 0x42D6BCC41E900000,
    0x430C6BF526340000, 0x430C6BF526340008, 0x430C6BF526340050, 0x430C6BF526340320,
    0x430C6BF526341F40, 0x430C6BF526353880, 0x430C6BF526403500, 0x430C6BF526AE1200,
    0x430C6BF52AF8B400, 0x430C6BF555E30800, 0x430C6BF7030A5000, 0x430C6C07C6932000,
    0x430C6CAF69EB4000, 0x430C733BCB5C8000, 0x430CB4B799C90000, 0x430F438DAA060000,
    0x4020000000000000, 0x4050000000000000, 0x4080000000000000, 0x40C0000000000000,
    0x40F0000000000000, 0x4120000000000000, 0x4160000000000000, 0x4190000000000000,
    0x41C0000000000000, 0x4200000000000000, 0x4230000000000000, 0x4260000000000000,
    0x42A0000000000000, 0x42D0000000000000, 0x4300000000000000, 0x40BF400000000000,
    0x40EF400000000000, 0x411F400000000000, 0x415F400000000000, 0x418F400000000000,
    0x41BF400000000000, 0x41FF400000000000, 0x422F400000000000, 0x425F400000000000,
    0x429F400000000000, 0x42CF400000000000, 0x42FF400000000000, 0x433F400000000000,
    0x3810000000000000, 0x47EFFFFFE0000000, 0x36A0000000000000, 0x4180000080000000,
    0x4200C388C0000000, 0x422000D500000000, 0x4112A3F080000000, 0x40BFA30800000000,
    0x3F30000000000000, 0x3F64000000000000, 0x3F72000000000000, 0x3F7A000000000000,
    0x4470000000000000, 0x4170000000000000, 0x4180000020000000, 0x41900161A0000000,
    0x381A48B080000000, 0xB716000000000000, 0x381B217100000000, 0x40B007E680000000,
    0x41F3E49EE0000000, 0x380093F880000000, 0x3F50E45860000000, 0x4390000820000000,
    0x3AB5C87FA0000000, 0x43A9999F60000000, 0x4190000020000000, 0x36CC000000000000,
    0x42F001DB00000000, 0x43E0000000000000, 0x4600001E00000000, 0x43E47D3580000000,
    0x43D2A05F20000000, 0x43D0025620000000, 0x3F80000500000000, 0x4419BD0C20000000,
    0x3875454A00000000, 0x4069000000000000, 0x4180000000000000, 0x43A2A05F20000000,
    0x43B2A05F20000000, 0x43C2A05F20000000, 0x3FF3333340000000, 0x3FF3AE1480000000,
    0x3FF3BE76C0000000, 0x3FF3C08320000000, 0x3FF3C0C200000000, 0x3FF3C0C960000000,
    0x3FF3C0CA20000000, 0x387A419FC0000000, 0x4310000000000001, 0x4310000000000003,
]

def build_adversarial() -> list[float]:
    out: list[float] = []

    # The full Ryu test corpus, first (superset guarantee).
    out += [u2f(b) for b in RYU_SUITE_BITS]

    # Original 23
    out += [
        0.0, 1.0, -1.0, 0.1, 1.5, 2.5, 3.5, 4.5,
        1.234567890123456e-10, 6.123456789012345e15,
        1.7976931348623157e308, 5e-324, 2.2250738585072014e-308,
        9.999999999999998e+22, 1.7976931348623155e308,
        12345.6789, -0.0001, 1e-100, 1e+100,
        3.141592653589793, 2.718281828459045,
        1.0000000000000002, 0.30000000000000004,
    ]

    # Ryu / Schubfach hand-curated edge cases (lifted from Tests/Ryu.lean).
    out += [
        u2f(0x7FEFFFFFFFFFFFFF),  # max finite normal
        u2f(0x0000000000000001),  # min positive subnormal
        2.9802322387695312e-8,
        -2.109808898695963e16,
        4.940656e-318, 1.18575755e-316, 2.989102097996e-312,
        9.0608011534336e15, 4.708356024711512e18, 9.409340012568248e18,
        1.2345678,
        # LooksLikePow5
        u2f(0x4830F0CF064DD592), u2f(0x4840F0CF064DD592), u2f(0x4850F0CF064DD592),
        # OutputLength digit progression
        1.2, 1.23, 1.234, 1.2345, 1.23456, 1.234567, 1.23456789,
        1.234567895, 1.2345678901, 1.23456789012, 1.234567890123,
        1.2345678901234, 1.23456789012345, 1.234567890123456,
        1.2345678901234567,
        # 2^32 neighbourhood
        4.294967294, 4.294967295, 4.294967296, 4.294967297, 4.294967298,
        # MinMaxShift IEEE-constructed
        u2f((4 << 52)),                              # exp=4, mant=0
        u2f((6 << 52) | ((1 << 52) - 1)),            # exp=6, max mantissa
        u2f((41 << 52)),
        u2f((40 << 52) | ((1 << 52) - 1)),
        u2f((1077 << 52)),
        u2f((1076 << 52) | ((1 << 52) - 1)),
        u2f((307 << 52)),
        u2f((306 << 52) | ((1 << 52) - 1)),
        u2f((934 << 52) | 0x000FA7161A4D6E0C),
        # 2^53 boundary
        9007199254740991.0, 9007199254740992.0,
        # Pure powers of 10
        1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8, 1e9,
        1e10, 1e11, 1e12, 1e13, 1e14, 1e15,
        # Largest power of 2 below 10^(i+1)
        8.0, 64.0, 512.0, 8192.0, 65536.0, 524288.0, 8388608.0,
        67108864.0, 536870912.0, 8589934592.0,
    ]

    # ulp boundaries around powers of 2
    for k in [-10, -2, -1, 0, 1, 2, 3, 4, 10, 20, 50, 100, 200, 1000]:
        p = 2.0 ** k
        u = f2u(p)
        out += [p, u2f(u - 1), u2f(u + 1)]

    # 0.1 + 0.2 family
    out += [0.1 + 0.2, 0.1 * 3, 0.3, 0.7 - 0.4, 1.0 / 3.0, 2.0 / 3.0]

    # tiny but not subnormal
    out += [u2f(0x0010000000000000),  # smallest normal
            u2f(0x0010000000000001),
            u2f(0x000FFFFFFFFFFFFF)]  # largest subnormal

    # de-dupe by bit pattern, preserving order; drop non-finite.
    seen = set()
    deduped: list[float] = []
    for f in out:
        u = f2u(f)
        if not is_finite_u64(u):
            continue
        if u in seen:
            continue
        seen.add(u)
        deduped.append(f)
    return deduped


# ---------------------------------------------------------------------------
# Corpus: nice
# ---------------------------------------------------------------------------
# Stratified mix mirroring typical JSON / API payload distribution.

def build_nice(n: int = 1024) -> list[float]:
    """Synthetic model of practically-occurring values (JSON/API payloads).

    Five purely parametric strata -- each a stated distribution, no
    hand-enumerated values (curated values belong to `adversarial`):
      45% small integers in [0, 10000]            (counts, ids, sizes)
      20% 2-decimal fixed-point in [0.01, 1e5]    (currency-style)
      10% coordinates in [-180, 180], 4-6 decimals (lat/long-style)
      10% epoch-seconds in [1e9, 2e9], half with .ms (timestamp-style)
      15% scientific-range (full-precision computation results):
          mant * 10^e, mant ~ U[1, 10), e ~ U{-6..6}
    """
    rng = random.Random(SEED ^ 0x4E696365)  # "Nice"
    out: list[float] = []

    # 45% small integers in [0, 10000]
    for _ in range(int(n * 0.45)):
        out.append(float(rng.randint(0, 10000)))

    # 20% 2-decimal fixed-point in [0.01, 100000.00]
    for _ in range(int(n * 0.20)):
        cents = rng.randint(1, 10_000_000)
        out.append(cents / 100.0)

    # 10% latitude / longitude in [-180.0, 180.0] with 4-6 decimals
    for _ in range(int(n * 0.10)):
        decimals = rng.choice([4, 5, 6])
        scale = 10 ** decimals
        raw = rng.randint(-180 * scale, 180 * scale)
        out.append(raw / scale)

    # 10% epoch seconds as floats in [1e9, 2e9]; half integer-valued,
    # half with millisecond fractional component
    for i in range(int(n * 0.10)):
        secs = rng.randint(1_000_000_000, 2_000_000_000)
        if i % 2 == 0:
            out.append(float(secs))
        else:
            millis = rng.randint(0, 999)
            out.append(secs + millis / 1000.0)

    # 15% scientific-range: mant * 10^e (full-precision)
    while len(out) < n:
        mant = rng.uniform(1.0, 9.9999)
        exp = rng.randint(-6, 6)
        out.append(mant * (10 ** exp))

    # truncate / shuffle deterministically
    out = out[:n]
    rng.shuffle(out)
    return out


# ---------------------------------------------------------------------------
# Corpus: uniform
# ---------------------------------------------------------------------------
# Random finite binary64 values: uniform random IEEE bits filtered for finite.

def build_uniform(n: int = 1024) -> list[float]:
    rng = random.Random(SEED ^ 0x556E6966)  # "Unif"
    out: list[float] = []
    while len(out) < n:
        # Pick sign + biased exponent + mantissa uniformly.
        sign = rng.randint(0, 1)
        # Biased exponent in [1, 2046] (skip 0=zero/subnormal cluster and 2047=NaN/inf)
        # The original spec asks for q in [-1074, 1023] which translates to biased
        # exponent in [0, 2046]; we include subnormals by allowing exp=0 with random
        # nonzero mantissa.
        exp_choice = rng.randint(0, 2046)
        mantissa = rng.randint(0, (1 << 52) - 1)
        if exp_choice == 0 and mantissa == 0:
            continue  # skip +0 (we don't want the corpus dominated by zeros)
        bits = (sign << 63) | (exp_choice << 52) | mantissa
        if not is_finite_u64(bits):
            continue
        out.append(u2f(bits))
    return out


# ---------------------------------------------------------------------------
# Build the three corpora
# ---------------------------------------------------------------------------

adversarial: list[float] = build_adversarial()
nice: list[float] = build_nice(1024)
uniform: list[float] = build_uniform(1024)


# ---------------------------------------------------------------------------
# Emitters
# ---------------------------------------------------------------------------

LEAN_HEADER = """\
-- AUTO-GENERATED by benches/gen_corpora.py. DO NOT EDIT BY HAND.
-- Regenerate via: python3 benches/gen_corpora.py
--
-- Each float is reconstructed from its IEEE-754 u64 bit pattern,
-- guaranteeing bit-identity with the C++ and Python corpora.
"""

CPP_HEADER_GUARD = "BENCHES_CORPORA_H"

def emit_lean(path: str) -> None:
    lines = [LEAN_HEADER, "", "namespace Corpora", ""]
    for name, arr in [("adversarial", adversarial),
                      ("nice", nice),
                      ("uniform", uniform)]:
        lines.append(f"def {name} : Array Float := #[")
        items = [f"  Float.ofBits 0x{f2u(f):016X}" for f in arr]
        # 1 entry per line is verbose but trivially diffable.
        lines.append(",\n".join(items))
        lines.append("]")
        lines.append("")
    lines.append("end Corpora")
    lines.append("")
    with open(path, "w") as f:
        f.write("\n".join(lines))


def emit_cpp_header(path: str) -> None:
    with open(path, "w") as f:
        f.write(f"// AUTO-GENERATED by benches/gen_corpora.py. DO NOT EDIT BY HAND.\n")
        f.write(f"// Regenerate via: python3 benches/gen_corpora.py\n")
        f.write(f"#ifndef {CPP_HEADER_GUARD}\n")
        f.write(f"#define {CPP_HEADER_GUARD}\n")
        f.write("#include <cstdint>\n#include <vector>\n\n")
        f.write("namespace benches_corpora {\n")
        f.write("extern const std::vector<double> adversarial;\n")
        f.write("extern const std::vector<double> nice;\n")
        f.write("extern const std::vector<double> uniform;\n")
        f.write("}\n\n")
        f.write(f"#endif\n")


def emit_cpp_impl(path: str) -> None:
    with open(path, "w") as f:
        f.write("// AUTO-GENERATED by benches/gen_corpora.py. DO NOT EDIT BY HAND.\n")
        f.write("// Regenerate via: python3 benches/gen_corpora.py\n")
        f.write('#include "corpora.h"\n')
        f.write("#include <bit>\n\n")
        f.write("namespace benches_corpora {\n\n")
        f.write("static inline double from_bits(uint64_t u) { return std::bit_cast<double>(u); }\n\n")
        for name, arr in [("adversarial", adversarial),
                          ("nice", nice),
                          ("uniform", uniform)]:
            f.write(f"const std::vector<double> {name} = {{\n")
            for x in arr:
                f.write(f"  from_bits(0x{f2u(x):016X}ULL),\n")
            f.write("};\n\n")
        f.write("}\n")


def emit_java(path: str) -> None:
    with open(path, "w") as f:
        f.write("// AUTO-GENERATED by benches/gen_corpora.py. DO NOT EDIT BY HAND.\n")
        f.write("// Regenerate via: python3 benches/gen_corpora.py\n")
        f.write("public final class Corpora {\n")
        f.write("  private Corpora() {}\n")
        f.write("  private static double fb(long u) { return Double.longBitsToDouble(u); }\n\n")
        for name, arr in [("adversarial", adversarial),
                          ("nice", nice),
                          ("uniform", uniform)]:
            f.write(f"  public static final double[] {name} = {{\n")
            for x in arr:
                f.write(f"    fb(0x{f2u(x):016X}L),\n")
            f.write("  };\n\n")
        f.write("  public static double[] get(String label) {\n")
        f.write('    switch (label) {\n')
        f.write('      case "nice": return nice;\n')
        f.write('      case "uniform": return uniform;\n')
        f.write('      default: return adversarial;\n')
        f.write("    }\n  }\n}\n")


def emit_u64(dir_: str) -> None:
    """Plain u64-per-line corpus files for *external* benchmark harnesses
    (e.g. ref/ryu-lean4) that aren't part of this build. One file per corpus;
    each line is a decimal IEEE-754 bit pattern. Same bytes as every other
    emit, so checksums match."""
    os.makedirs(dir_, exist_ok=True)
    for name, arr in [("adversarial", adversarial), ("nice", nice), ("uniform", uniform)]:
        with open(os.path.join(dir_, f"{name}.u64"), "w") as f:
            for x in arr:
                f.write(f"{f2u(x)}\n")


def emit_all() -> None:
    here = os.path.dirname(os.path.abspath(__file__))
    emit_lean(os.path.join(here, "Corpora.lean"))
    emit_cpp_header(os.path.join(here, "corpora.h"))
    emit_cpp_impl(os.path.join(here, "corpora.cpp"))
    emit_java(os.path.join(here, "bench_java", "Corpora.java"))
    emit_u64(os.path.join(here, "corpora"))
    print(f"# generated:")
    print(f"#   adversarial: {len(adversarial)} entries")
    print(f"#   nice:        {len(nice)} entries")
    print(f"#   uniform:     {len(uniform)} entries")


# Stable checksum used by run.sh to verify all three impls see identical data.
def checksum(arr: list[float]) -> int:
    s = 0
    for x in arr:
        s = (s + f2u(x)) & 0xFFFFFFFFFFFFFFFF
    return s


def print_checksums() -> None:
    print(f"adversarial: n={len(adversarial)} sum_bits=0x{checksum(adversarial):016X}")
    print(f"nice:        n={len(nice)} sum_bits=0x{checksum(nice):016X}")
    print(f"uniform:     n={len(uniform)} sum_bits=0x{checksum(uniform):016X}")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--checksum":
        print_checksums()
    else:
        if "--seed" in sys.argv:
            SEED = int(sys.argv[sys.argv.index("--seed") + 1], 0)
        else:
            SEED = secrets.randbits(64)
        nice = build_nice(1024)
        uniform = build_uniform(1024)
        os.makedirs(os.path.dirname(_SEED_FILE), exist_ok=True)
        with open(_SEED_FILE, "w") as f:
            f.write(f"0x{SEED:016X}\n")
        print(f"# seed: 0x{SEED:016X}")
        emit_all()
        print_checksums()
