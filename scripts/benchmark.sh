#!/bin/bash
# Benchmark Lean factor vs sympy on test_cases.csv
# Usage: bash scripts/benchmark.sh [max_seconds_per_case]
set -euo pipefail

MAX_SEC=${1:-30}
FACTOR=.lake/build/bin/factor
CSV=scripts/test_cases.csv

echo "n,digits,lean_ms,sympy_ms,ratio,lean_factors,match"
tail -n +3 "$CSV" | while IFS=, read -r n digits factors sympy_ms; do
    # Lean (single run — process startup is ~5ms, negligible)
    lean_start=$(date +%s%N)
    lean_out=$(timeout "$MAX_SEC" "$FACTOR" "$n" 2>/dev/null) || lean_out="TIMEOUT"
    lean_end=$(date +%s%N)
    lean_ms=$(( (lean_end - lean_start) / 1000000 ))

    # Format lean output to match sympy format
    lean_factors=$(echo "$lean_out" | awk '{if ($2>1) printf "%s^%s ", $1, $2; else printf "%s ", $1}' | sed 's/ $//')

    # Compare
    if [ "$lean_factors" = "$factors" ]; then
        match="OK"
    else
        match="MISMATCH"
    fi

    # Ratio
    if [ "$sympy_ms" = "0.0" ]; then
        ratio="--"
    else
        ratio=$(python3 -c "print(f'{$lean_ms/$sympy_ms:.1f}x')" 2>/dev/null || echo "?")
    fi

    echo "$n,$digits,$lean_ms,$sympy_ms,$ratio,$lean_factors,$match"
done
