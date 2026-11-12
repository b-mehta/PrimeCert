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
# Kernel checking runs on this thread rather than asynchronously, because the asynchronous check
# holds several windows' worth of environment at once. Measured on a quiet box, alternated on off
# off on: peak 4.85 GB against 1.64, for the same processor seconds (74.6 against 73.7) and 7
# percent more wall clock. A run packs windows onto a machine, so the peak is what decides how
# many fit: a 14 GB runner takes four windows instead of two and a 64 GB box is left core-bound
# rather than memory-bound, which is twice the throughput and more. Set ASYNC=1 to measure the
# other way.
#
# Two peak figures are reported. `peak` is `/usr/bin/time`'s maximum resident set size for the lean
# process it launches; `sampled tree peak` is the largest half-second sample of that process plus
# its children summed. They agree while lean stays a single process, and the second is the one to
# compare with figures from a job that runs lean under another program.
#
# Reported per case: the sum of every [Kernel] entry; the sum over the window's batch lemmas
# (names containing `segEqV_…step_`), with those settled by sorting the batch's hits into slices
# (`segEqV_…sstep_`) and those of the widest band, where a divisor strikes at most twice
# (`segEqV_…wstep_`), each reported apart; the sum over its base-sieve slice lemmas
# (`segEqV_…chunk_`);
# wall clock and peak resident memory of lean from /usr/bin/time; the number of batch lemmas.
set +e +o pipefail
rounds=$1
shift
cases=("$@")
n=${#cases[@]}
limit=${LIMIT_KB:-14000000}
export LEAN_PATH=$(lake env printenv LEAN_PATH)

# Allocator settings for the lean process. Measured on a quiet 32 vCPU box, four runs an arm
# alternating: kernel 76.5-77.8 s without against 67.7-68.4 s with, processor 84.7-86.1 against
# 75.8-76.5, peak unchanged. Nothing in the project changes, so this is on by default and
# TUNE=0 turns it off, which is how the pair above was measured.
if [ "${TUNE:-1}" = "1" ]; then
  export GLIBC_TUNABLES=${GLIBC_TUNABLES:-glibc.malloc.mmap_threshold=33554432:glibc.malloc.trim_threshold=17179869184:glibc.malloc.top_pad=268435456}
fi

# The asynchronous kernel check costs three times the peak for nothing, as the header explains.
if [ "${ASYNC:-0}" = "0" ]; then
  case "$LEAN_FLAGS" in
    *Elab.async*) ;;
    *) LEAN_FLAGS="-DElab.async=false $LEAN_FLAGS" ;;
  esac
fi

# These cases call lean directly rather than through lake, so nothing hands it the shared objects
# the precompiled libraries build. Without the flags below that code runs in the interpreter
# whatever the lakefile says. A library the lakefile does not precompile leaves no object, so this
# names exactly the ones there are.
# Named rather than globbed. A glob over libPrimeCert_*.so also picks up a shared object another
# project left in this build tree, and lean then exits 127 on an undefined symbol before it
# measures anything, which reads as a failed case rather than a poisoned run. So this lists the
# libraries this lakefile precompiles, and stops on any other object rather than loading it.
precompiled="SieveEmit"
plugin=""
for lib in $precompiled; do
  so=".lake/build/lib/libPrimeCert_$lib.so"
  if [ ! -f "$so" ]; then
    echo "run.sh: $so is missing; run lake build $lib first" >&2
    exit 1
  fi
  plugin="$plugin --plugin=$so"
done
for so in .lake/build/lib/libPrimeCert_*.so; do
  [ -f "$so" ] || continue
  case " $precompiled " in
    *" $(basename "$so" .so | sed 's/^libPrimeCert_//') "*) ;;
    *) echo "run.sh: $so is not one of this project's precompiled libraries ($precompiled); \
delete it or add it to the list" >&2; exit 1 ;;
  esac
done

# ksum <file> <pattern>: the sum of the [Kernel] seconds on lines matching the pattern.
ksum() {
  grep -o "\[Kernel\] \[[0-9.]*\].*$2" "$1" | grep -o '^\[Kernel\] \[[0-9.]*\]' \
    | grep -o '[0-9]\+\.[0-9]\+' | awk '{s+=$1} END {printf "%.3f", s}'
}

# cmdsum <file> <command>: the seconds the profiler charges to the commands whose text starts with
# <command>. `elab command` below covers the whole file, so this is how the base sieve and the
# window are told apart, each of which the elaborator builds in code of ours that may or may not
# be compiled.
cmdsum() {
  grep -oE "^\[Elab.command\] \[[0-9.]+\][^[]*$2" "$1" | grep -oE '\[[0-9]+\.[0-9]+\]' \
    | tr -d '[]' | awk '{s+=$1} END {printf "%.3f", s+0}'
}

# esum <file> <tag>: the sum of the seconds on lines whose profiler tag is <tag>, e.g. Elab.command
# or Elab.step. These cover the elaborator rather than the kernel.
esum() {
  grep -o "\[$2\] \[[0-9.]*\]" "$1" | grep -o '[0-9]\+\.[0-9]\+' \
    | awk '{s+=$1} END {printf "%.3f", s+0}'
}

for round in $(seq 1 "$rounds"); do
  for k in $(seq 0 $((n - 1))); do
    f=${cases[$(( (k + round - 1) % n ))]}
    out="out-${TAG}$f-$round.txt"
    tim="time-${TAG}$f-$round.txt"
    /usr/bin/time -v lean $plugin -Dtrace.profiler=true -Dtrace.profiler.threshold=0 $LEAN_FLAGS \
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
    steps=$(ksum "$out" "segEqV_.*[^sw]step_")
    sorted=$(ksum "$out" "segEqV_.*sstep_")
    wide=$(ksum "$out" "segEqV_.*wstep_")
    chunks=$(ksum "$out" "segEqV_.*chunk_")
    elab=$(esum "$out" "Elab.command")
    basecmd=$(cmdsum "$out" "run_sieve")
    wincmd=$(cmdsum "$out" "run_segment")
    addd=$(esum "$out" "addDecl")
    typec=$(esum "$out" "typechecking")
    wall=$(grep 'Elapsed (wall clock)' "$tim" | awk '{print $8}')
    cpu=$(grep -E 'User time|System time' "$tim" | awk '{s += $NF} END {printf "%.1f", s}')
    peak=$(grep 'Maximum resident set size' "$tim" | awk '{print $6}')
    nsteps=$(grep -c 'typechecking declarations \[.*segEqV_.*step_' "$out")
    # The emitter's own report of how long it spent sorting batches into slices, which is the part
    # of the non-kernel remainder that the compiled twins are responsible for.
    sortms=$(grep -oE 'stripeSort total [0-9]+ ms' "$out" | awk '{s += $3} END {printf "%d", s}')
    twinms=$(grep -oE 'segLoopC total [0-9]+ ms' "$out" | awk '{s += $3} END {printf "%d", s+0}')
    echo "round $round | ${TAG}$f | kernel total ${total}s | batch lemmas ${steps}s | sorted" \
      "batch lemmas ${sorted}s | wide band lemmas ${wide}s | slice lemmas ${chunks}s |" \
      "elab command ${elab}s | base sieve ${basecmd}s | window ${wincmd}s |" \
      "addDecl ${addd}s | typechecking ${typec}s | stripeSort ${sortms}ms |" \
      "segLoopC ${twinms}ms |" \
      "wall $wall | processor ${cpu}s | peak ${peak} KiB | sampled tree peak ${sampled} KiB |" \
      "batch lemma count $nsteps"
  done
done
