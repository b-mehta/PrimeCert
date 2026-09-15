#!/usr/bin/env bash
# Usage: run.sh <rounds> <case>...
# Times each case file PrimeCertTest/SegTune/<case>.lean, all cases once per round, rounds in
# sequence, and appends every failed case to bench-failures.txt. Each lean process runs under an
# address-space cap of CAP_KB kibibytes (default 15000000), so a case that outgrows the runner
# fails on its own and the job carries on.
set +e +o pipefail
rounds=$1
shift
cap=${CAP_KB:-15000000}
export LEAN_PATH=$(lake env printenv LEAN_PATH)
for round in $(seq 1 "$rounds"); do
  for f in "$@"; do
    out="out-$f-$round.txt"
    tim="time-$f-$round.txt"
    ( ulimit -v "$cap"; ulimit -c 0
      /usr/bin/time -v lean -Dtrace.profiler=true -Dtrace.profiler.threshold=1 \
        "PrimeCertTest/SegTune/$f.lean" > "$out" 2> "$tim" )
    status=$?
    if [ "$status" -ne 0 ]; then
      echo "RUN FAILED $f round $round exit $status" | tee -a bench-failures.txt
      grep -E 'error' "$out" | head -5
    fi
    total=$(grep -o '\[Kernel\] \[[0-9.]*\]' "$out" | grep -o '[0-9]\+\.[0-9]\+' \
      | awk '{s+=$1} END {printf "%.3f", s}')
    wall=$(grep 'Elapsed (wall clock)' "$tim" | awk '{print $8}')
    peak=$(grep 'Maximum resident set size' "$tim" | awk '{print $6}')
    steps=$(grep -c 'typechecking declarations \[.*step_' "$out")
    echo "round $round | $f | kernel total ${total}s | wall $wall | peak ${peak} KiB | step lemmas $steps"
  done
done
