#!/usr/bin/env python3
"""Fully reproducible cross-impl Float->String performance graph.

Builds every implementation, asserts they all see *bit-identical* inputs
(checksum gate), times each over the committed corpora pinned to one core,
then emits a CSV and a bar chart.

Implementations compared (all compute the shortest round-tripping decimal):
  - Lean (this repo)   — our verified Schubfach
  - JDK (Schubfach)    — Double.toString, the reference Schubfach (JDK 19+)
  - to_chars (+string) — libstdc++ std::to_chars + std::string per call;
                         allocation-matched to Lean/JDK/CPython, which all
                         return a fresh heap string per call
  - CPython repr       — interpreter built-in
  - snprintf %.17g     — libc (NOT shortest; included only with --snprintf)

The non-competitive references (pure-Nat spec path, ryu-lean4) were dropped
from the plot; linear scale shows the competitive field directly.

Inputs come from benches/gen_corpora.py (single source of truth, fixed seed),
serialised as u64 bit patterns; every impl reconstructs the same floats.

Run (from repo root):
    python3 benches/plot.py                 # all corpora, writes perf.png + results.csv
    python3 benches/plot.py --corpus uniform
    python3 benches/plot.py --snprintf      # also include libc snprintf

Outputs: benches/results.csv, benches/perf.png
Numbers vary +-15% with thermal/load; re-run for stability.
"""
import argparse
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
PIN = ["taskset", "-c", os.environ.get("BENCH_CORE", "0")]
# Ordered by output difficulty: short payload-style outputs first, then
# full-precision random bit patterns, then curated edge cases.
ALL_CORPORA = ["nice", "uniform", "adversarial"]

# label -> (argv builder, checksum argv builder, env). cwd is repo root.
def impls(include_snprintf):
    d = {
        "Lean (this repo)": (
            lambda c: PIN + ["./.lake/build/bin/benchFloatToString", c],
            lambda c: ["./.lake/build/bin/benchFloatToString", c, "--checksum"], None),
        "JDK (Schubfach)": (
            lambda c: PIN + ["java", "-cp", "benches/bench_java", "Bench", c],
            lambda c: ["java", "-cp", "benches/bench_java", "Bench", c, "--checksum"], None),
        # std::to_chars + std::string per call: allocation-matched to the
        # Lean/Java/Python harnesses, which all return a fresh heap string.
        # (bench_ref's bare "chars" mode writes into one reused stack buffer;
        # it stays available as the load canary but is not plotted.)
        "to_chars (+string)": (
            lambda c: PIN + ["./benches/bench_ref", "chars_str", c],
            lambda c: ["./benches/bench_ref", "chars_str", c, "--checksum"], None),
        "CPython repr": (
            lambda c: PIN + ["python3", "benches/bench_py.py", c],
            lambda c: ["python3", "benches/bench_py.py", c, "--checksum"], None),
    }
    if include_snprintf:
        d["snprintf %.17g"] = (
            lambda c: PIN + ["./benches/bench_ref", "snprintf", c],
            lambda c: ["./benches/bench_ref", "chars", c, "--checksum"], None)  # same inputs
    return d


def sh(cmd, env=None):
    e = {**os.environ, **env} if env else None
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True,
                          check=True, env=e).stdout


def build():
    print("== building ==", flush=True)
    sh(["python3", "benches/gen_corpora.py"])   # ensure corpora/*.u64 exist
    sh(["lake", "build", "benchFloatToString"])
    sh(["g++", "-O3", "-std=c++20", "-march=native", "-o", "benches/bench_ref",
        "benches/bench_ref.cpp", "benches/corpora.cpp"])
    sh(["javac", "benches/bench_java/Bench.java", "benches/bench_java/Corpora.java",
        "-d", "benches/bench_java"])


def sum_bits(out):
    m = re.search(r"sum_bits=(\d+)", out)
    return m.group(1) if m else None


def median_ns(out):
    m = re.search(r"median\s*=\s*(\d+)", out)
    if not m:
        raise RuntimeError(f"no median in output:\n{out}")
    return int(m.group(1))


def load_csv():
    """Read results.csv -> (results dict, ordered impl names, ordered corpora)."""
    path = os.path.join(HERE, "results.csv")
    results, names, corpora = {}, [], []
    with open(path) as f:
        next(f)  # header
        for line in f:
            name, c, ns = line.rstrip("\n").rsplit(",", 2)
            results[(name, c)] = int(ns)
            if name not in names:
                names.append(name)
            if c not in corpora:
                corpora.append(c)
    return results, names, corpora


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", choices=ALL_CORPORA, action="append",
                    help="restrict to corpus (repeatable); default all")
    ap.add_argument("--snprintf", action="store_true", help="also bench libc snprintf")
    ap.add_argument("--no-build", action="store_true")
    ap.add_argument("--replot", action="store_true",
                    help="redraw from existing results.csv (no build, no timing)")
    args = ap.parse_args()

    if args.replot:
        results, names, corpora = load_csv()
        plot(results, names, corpora)
        return

    corpora = args.corpus or ALL_CORPORA
    impl = impls(args.snprintf)

    if not args.no_build:
        build()

    # --- checksum gate: every impl must see identical inputs -----------------
    print("== input sanity (all impls must agree per corpus) ==", flush=True)
    for c in corpora:
        sums = {name: sum_bits(sh(mk_chk(c), env)) for name, (_, mk_chk, env) in impl.items()}
        uniq = set(v for v in sums.values() if v is not None)
        if len(uniq) != 1:
            print(f"  {c}: MISMATCH {sums}")
            sys.exit("ABORT: bit-identical input invariant violated")
        print(f"  {c}: OK sum_bits={uniq.pop()}")

    # --- time ----------------------------------------------------------------
    print(f"== timing (median ns/call, pinned core {os.environ.get('BENCH_CORE', '0')}) ==", flush=True)
    results = {}  # (impl, corpus) -> ns
    for c in corpora:
        for name, (mk_run, _, env) in impl.items():
            ns = median_ns(sh(mk_run(c), env))
            results[(name, c)] = ns
            print(f"  {name:22s} {c:12s} {ns:8d} ns", flush=True)

    # --- CSV -----------------------------------------------------------------
    csv_path = os.path.join(HERE, "results.csv")
    with open(csv_path, "w") as f:
        f.write("impl,corpus,ns_per_call\n")
        for (name, c), ns in results.items():
            f.write(f"{name},{c},{ns}\n")
    print(f"wrote {csv_path}")

    plot(results, list(impl.keys()), corpora)


def plot(results, names, corpora):
    import matplotlib
    matplotlib.use("Agg")
    # Match the dissertation body font (XeLaTeX + fontspec \setmainfont{LinLibertine}).
    # Embedded as PDF so text is vector and Type-42 (selectable, no Type-3).
    matplotlib.rcParams.update({
        "font.family": "serif",
        "font.serif": ["Linux Libertine O"],
        "pdf.fonttype": 42,
        "svg.fonttype": "none",
        # Large text so the figure stays legible when embedded below \textwidth.
        "font.size": 18,
    })
    import matplotlib.pyplot as plt
    import numpy as np

    # Legend labels: languages (algorithm/library provenance goes in the caption).
    display = {
        "to_chars (+string)": "C++",
        "JDK (Schubfach)": "Java",
        "Lean (this repo)": "Lean (this work)",
        "CPython repr": "CPython",
        "snprintf %.17g": "C (snprintf)",
    }

    # Display order: fastest-first, grouped left-to-right.
    order = ["to_chars (+string)", "JDK (Schubfach)", "Lean (this repo)",
             "CPython repr", "snprintf %.17g"]
    names = sorted(names, key=lambda n: order.index(n) if n in order else len(order))

    x = np.arange(len(corpora))
    w = 0.8 / len(names)
    # Okabe-Ito colour-blind-safe palette. Lean (this work) in the anchor blue;
    # CPython in vermillion so the tall "production interpreter" bar reads as
    # the outlier we beat; C++/Java in distinct neutral-ish hues.
    colors = {
        "to_chars (+string)": "#E69F00",  # orange
        "JDK (Schubfach)": "#009E73",     # bluish green
        "Lean (this repo)": "#0072B2",    # blue (this work)
        "CPython repr": "#D55E00",        # vermillion
        "snprintf %.17g": "#999999",      # grey
    }
    fig, ax = plt.subplots(figsize=(9, 5.2))
    for i, name in enumerate(names):
        vals = [results[(name, c)] for c in corpora]
        bars = ax.bar(x + i * w - 0.4 + w / 2, vals, w,
                      label=display.get(name, name), color=colors.get(name, None))
        for b, v in zip(bars, vals):
            ax.annotate(f"{v}", (b.get_x() + b.get_width() / 2, v),
                        ha="center", va="bottom", fontsize=13,
                        xytext=(0, 2), textcoords="offset points")
    ax.set_ylabel("ns / call")
    ax.set_xticks(x)
    ax.set_xticklabels(corpora)
    ax.legend(frameon=False, fontsize=17, loc="upper left")
    ax.grid(axis="y", which="both", alpha=0.25, linewidth=0.5)
    ax.set_axisbelow(True)
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    fig.tight_layout()
    for ext, kw in (("pdf", {}), ("png", {"dpi": 140}), ("svg", {})):
        out = os.path.join(HERE, f"perf.{ext}")
        fig.savefig(out, **kw)
        print(f"wrote {out}")


if __name__ == "__main__":
    main()
