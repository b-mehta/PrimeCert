#!/usr/bin/env bash
# Usage: tune-ab.sh <rounds> <case>...
#
# Times each case with and without a set of glibc malloc tunables on the lean process, alternating
# the arms on one machine in the order plain, tuned, tuned, plain, so neither arm always runs first
# or on a cold cache. Nothing in the project changes between the arms: the tunables are environment
# variables, so this prices the allocator settings and nothing else.
#
# The settings came from the goldbach agent, which measured them against a different workload. What
# they do to this one is what this script is for.
#
# Each arm's output carries TAG=P- or TAG=T-, so `run.sh`'s per-case files do not collide.
set +e +o pipefail
rounds=$1
shift
cases=("$@")

TUNABLES=glibc.malloc.mmap_threshold=33554432:glibc.malloc.trim_threshold=17179869184:glibc.malloc.top_pad=268435456

for r in $(seq 1 "$rounds"); do
  for arm in P T T P; do
    if [ "$arm" = "T" ]; then
      TAG="T$r-" GLIBC_TUNABLES="$TUNABLES" LEAN_FLAGS=-DElab.async=false \
        PrimeCertTest/SegTune/run.sh 1 "${cases[@]}"
    else
      TAG="P$r-" LEAN_FLAGS=-DElab.async=false PrimeCertTest/SegTune/run.sh 1 "${cases[@]}"
    fi
  done
done
