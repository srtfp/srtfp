#!/usr/bin/env bash
# Reproducible Float→String cross-impl benchmark.
#
# Compares (median ns/call, lower is better):
#   Lean Schubfach         — this repo (./BenchFloatToString.lean)
#   std::to_chars (Ryu)    — libstdc++ shortest-decimal
#   C snprintf("%.17g")    — POSIX libc
#   CPython repr(f)        — interpreter built-in
#
# Inputs are generated deterministically by benches/gen_corpora.py and
# committed as benches/{Corpora.lean,corpora.h,corpora.cpp}; all three
# impls reconstruct floats from u64 bit patterns, guaranteeing identity.
#
# Pin to a single core (taskset -c 0) to suppress migration noise.

set -euo pipefail
cd "$(dirname "$0")/.."

CORPORA=(adversarial nice uniform)
PIN="taskset -c ${BENCH_CORE:-0}"

echo "== Building benches =="
lake build benchFloatToString
g++ -O3 -std=c++20 -march=native -o benches/bench_ref \
    benches/bench_ref.cpp benches/corpora.cpp

echo
echo "== Cross-impl input sanity check =="
mismatch=0
for c in "${CORPORA[@]}"; do
    lean_chk=$(./.lake/build/bin/benchFloatToString "$c" --checksum)
    cpp_chk=$(./benches/bench_ref chars "$c" --checksum)
    py_chk=$(python3 benches/bench_py.py "$c" --checksum)
    printf "  %-12s  lean: %s | cpp: %s | py: %s\n" "$c" "$lean_chk" "$cpp_chk" "$py_chk"
    if [ "$lean_chk" != "$cpp_chk" ] || [ "$lean_chk" != "$py_chk" ]; then
        echo "  ERROR: $c checksums diverge across impls"
        mismatch=1
    fi
done
if [ "$mismatch" -ne 0 ]; then
    echo "ABORTING: bit-identical input invariant violated"
    exit 1
fi

declare -A R
run_one() {
    local impl="$1"; local corpus="$2"; local cmd="$3"
    local out; out=$(eval "$cmd")
    local ns; ns=$(echo "$out" | grep -oE 'median = [0-9]+' | grep -oE '[0-9]+')
    R["$impl,$corpus"]="$ns"
    printf "  %-12s %-12s %s\n" "$impl" "$corpus" "$out"
}

echo
echo "== Running =="
for c in "${CORPORA[@]}"; do
    run_one "lean"     "$c" "$PIN ./.lake/build/bin/benchFloatToString $c"
    run_one "chars"    "$c" "$PIN ./benches/bench_ref chars $c"
    run_one "snprintf" "$c" "$PIN ./benches/bench_ref snprintf $c"
    run_one "python"   "$c" "$PIN python3 benches/bench_py.py $c"
done

echo
echo "== Summary (median ns/call) =="
printf "| %-14s | %8s | %8s | %8s | %8s |\n" "Corpus" "Lean" "to_chars" "snprintf" "Python"
printf "|----------------|----------|----------|----------|----------|\n"
for c in "${CORPORA[@]}"; do
    printf "| %-14s | %8s | %8s | %8s | %8s |\n" \
        "$c" "${R[lean,$c]}" "${R[chars,$c]}" "${R[snprintf,$c]}" "${R[python,$c]}"
done

echo
echo "Done.  Numbers vary ±15% with thermal/load; re-run for stability."
