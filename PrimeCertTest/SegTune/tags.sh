#!/usr/bin/env bash
# Usage: tags.sh <profiler output file>...
# Sums the profiler's seconds by category, over the top-level entries only (a line starting in
# column 0), so nested entries are counted once through their parent. Prints one line per category,
# largest first, then the total. Pair it with the wall clock from run.sh: the gap between that wall
# clock and this total is time the profiler attributes to nothing.
set +e +o pipefail
for f in "$@"; do
  echo "== $f"
  grep -o '^\[[A-Za-z_.]*\] \[[0-9.]*\]' "$f" \
    | sed 's/\] \[/ /; s/^\[//; s/\]$//' \
    | awk '{s[$1] += $2} END {for (t in s) printf "%10.3f s  %s\n", s[t], t}' \
    | sort -rn
  grep -o '^\[[A-Za-z_.]*\] \[[0-9.]*\]' "$f" \
    | grep -o '\[[0-9.]*\]$' | tr -d '[]' \
    | awk '{s += $1} END {printf "%10.3f s  TOTAL\n", s}'
done
