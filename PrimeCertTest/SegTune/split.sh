#!/usr/bin/env bash
# Usage: split.sh <cut> <profiler output file>...
# Sums the [Kernel] seconds of the batch lemmas either side of batch number <cut>, so the run's
# kernel time can be attributed to the primes small enough for the mask to be doubled into place
# (batch number below <cut>) and the primes whose mask is its two seeds (at or above <cut>).
set +e +o pipefail
cut=$1
shift
for f in "$@"; do
  echo "== $f"
  grep -o '\[Kernel\] \[[0-9.]*\].*segEqV_[^ ]*step_[0-9]*' "$f" \
    | sed 's/.*\[Kernel\] \[\([0-9.]*\)\].*step_\([0-9]*\)/\1 \2/' \
    | awk -v c="$cut" '{ if ($2 < c) {a += $1; na++} else {b += $1; nb++} }
        END {printf "%6d lemmas below %d: %8.1f s\n%6d lemmas from %d up: %8.1f s\n",
             na, c, a, nb, c, b}'
done
