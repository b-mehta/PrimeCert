#!/usr/bin/env bash
# Usage: pair.sh <case> <case>
# Runs both cases at once in separate lean processes and reports the wall clock of the pair, each
# process's own peak, and the largest half-second sample of the two summed, which is what a runner
# has to hold. LEAN_FLAGS is passed to both.
set +e +o pipefail
export LEAN_PATH=$(lake env printenv LEAN_PATH)
start=$(date +%s)
pids=()
for f in "$@"; do
  /usr/bin/time -v lean $LEAN_FLAGS "PrimeCertTest/SegTune/$f.lean" \
    > "out-pair-$f.txt" 2> "time-pair-$f.txt" &
  pids+=($!)
done
summed=0
alive() { for p in "${pids[@]}"; do kill -0 "$p" 2>/dev/null && return 0; done; return 1; }
while alive; do
  total=0
  for p in "${pids[@]}"; do
    lp=$(pgrep -P "$p" 2>/dev/null)
    r=$(ps -o rss= -p $lp 2>/dev/null | awk '{s += $1} END {print s+0}')
    total=$((total + r))
  done
  if [ "$total" -gt "$summed" ]; then summed=$total; fi
  sleep 0.5
done
wait
finish=$(date +%s)
echo "pair wall $((finish - start)) s | summed tree peak ${summed} KiB"
for f in "$@"; do
  peak=$(grep 'Maximum resident set size' "time-pair-$f.txt" | awk '{print $6}')
  w=$(grep 'Elapsed (wall clock)' "time-pair-$f.txt" | awk '{print $8}')
  echo "  $f | wall $w | peak ${peak} KiB"
done
