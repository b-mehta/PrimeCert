#!/usr/bin/env bash
# Usage: run.sh <rounds> <case>...
# Times each case file PrimeCertTest/SegTune/<case>.lean. Every round runs every case once, and the
# first case moves along by one each round, so no case always runs first. Every failed case is
# appended to bench-failures.txt. A watchdog kills the lean process once its resident memory
# passes LIMIT_KB kibibytes (default 14000000), so a case that would exhaust the runner fails on
# its own and the job carries on.
#
# Two environment variables adjust a run: LEAN_FLAGS adds flags to the lean command line, and TAG
# prefixes the per-case output files, so two settings can run in one job without overwriting each
# other. LEAN_FLAGS=-Ddebug.skipKernelTC=true times the elaborator with the kernel check switched
# off.
#
# Two peak figures are reported. `peak` is `/usr/bin/time`'s maximum resident set size for the lean
# process it launches; `sampled tree peak` is the largest half-second sample of that process plus
# its children summed. They agree while lean stays a single process, and the second is the one to
# compare with figures from a job that runs lean under another program.
#
# Reported per case: the sum of every [Kernel] entry; the sum over the window's batch lemmas
# (names containing `segEqV_…step_`), with those settled by sorting the batch's hits into slices
# (`segEqV_…sstep_`) reported apart; the sum over its base-sieve slice lemmas (`segEqV_…chunk_`);
# wall clock and peak resident memory of lean from /usr/bin/time; the number of batch lemmas.
set +e +o pipefail
rounds=$1
shift
cases=("$@")
n=${#cases[@]}
limit=${LIMIT_KB:-14000000}
export LEAN_PATH=$(lake env printenv LEAN_PATH)

# ksum <file> <pattern>: the sum of the [Kernel] seconds on lines matching the pattern.
ksum() {
  grep -o "\[Kernel\] \[[0-9.]*\].*$2" "$1" | grep -o '^\[Kernel\] \[[0-9.]*\]' \
    | grep -o '[0-9]\+\.[0-9]\+' | awk '{s+=$1} END {printf "%.3f", s}'
}

for round in $(seq 1 "$rounds"); do
  for k in $(seq 0 $((n - 1))); do
    f=${cases[$(( (k + round - 1) % n ))]}
    out="out-${TAG}$f-$round.txt"
    tim="time-${TAG}$f-$round.txt"
    /usr/bin/time -v lean -Dtrace.profiler=true -Dtrace.profiler.threshold=0 $LEAN_FLAGS \
      "PrimeCertTest/SegTune/$f.lean" > "$out" 2> "$tim" &
    tpid=$!
    killed=0
    sampled=0
    while kill -0 "$tpid" 2>/dev/null; do
      lpid=$(pgrep -P "$tpid")
      tree=$(pgrep -P "$lpid" 2>/dev/null)
      rss=$(ps -o rss= -p "$lpid" $(echo "$tree" | tr '\n' ' ') 2>/dev/null \
        | awk '{s += $1} END {print s}')
      if [ -n "$rss" ] && [ "$rss" -gt "$sampled" ]; then
        sampled=$rss
      fi
      if [ -n "$rss" ] && [ "$rss" -gt "$limit" ]; then
        kill -9 "$lpid"
        killed=1
      fi
      sleep 0.5
    done
    wait "$tpid"
    status=$?
    if [ "$killed" -eq 1 ]; then
      echo "KILLED $f round $round: resident memory passed $limit KiB" | tee -a bench-failures.txt
    fi
    if [ "$status" -ne 0 ]; then
      echo "RUN FAILED $f round $round exit $status" | tee -a bench-failures.txt
      grep -E 'error' "$out" | head -5
    fi
    total=$(ksum "$out" "")
    steps=$(ksum "$out" "segEqV_.*[^s]step_")
    sorted=$(ksum "$out" "segEqV_.*sstep_")
    chunks=$(ksum "$out" "segEqV_.*chunk_")
    wall=$(grep 'Elapsed (wall clock)' "$tim" | awk '{print $8}')
    cpu=$(grep -E 'User time|System time' "$tim" | awk '{s += $NF} END {printf "%.1f", s}')
    peak=$(grep 'Maximum resident set size' "$tim" | awk '{print $6}')
    nsteps=$(grep -c 'typechecking declarations \[.*segEqV_.*step_' "$out")
    echo "round $round | ${TAG}$f | kernel total ${total}s | batch lemmas ${steps}s | sorted" \
      "batch lemmas ${sorted}s | slice lemmas ${chunks}s | wall $wall | processor ${cpu}s |" \
      "peak ${peak} KiB | sampled tree peak ${sampled} KiB | batch lemma count $nsteps"
  done
done
