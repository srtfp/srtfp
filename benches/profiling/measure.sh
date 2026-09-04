#!/usr/bin/env bash
# Repeat a bench command R times (default 5), pinned to one core, and print
# every median plus the min and median of those medians. The machine this
# was developed on is shared and noisy (other Lean/Python jobs), so a
# single 5-run median can swing ±30%; the min of several is the stable
# figure for before/after comparisons.
#
#   benches/profiling/measure.sh [-r R] [-c CORE] -- <cmd> [args...]
set -euo pipefail
R=5; CORE=5
while [ $# -gt 0 ]; do
  case "$1" in
    -r) R="$2"; shift 2 ;;
    -c) CORE="$2"; shift 2 ;;
    --) shift; break ;;
    *) break ;;
  esac
done
meds=()
for ((i = 0; i < R; i++)); do
  out=$(taskset -c "$CORE" "$@" 2>&1)
  m=$(printf '%s\n' "$out" | grep -oE 'median = [0-9]+(\.[0-9]+)?' | grep -oE '[0-9]+(\.[0-9]+)?' | head -1)
  meds+=("$m")
done
sorted=$(printf '%s\n' "${meds[@]}" | sort -n)
min=$(printf '%s\n' "$sorted" | head -1)
mid=$(printf '%s\n' "$sorted" | sed -n "$(( (R + 1) / 2 ))p")
printf '%-70s medians: %s | min %s | median %s\n' "$*" "${meds[*]}" "$min" "$mid"
