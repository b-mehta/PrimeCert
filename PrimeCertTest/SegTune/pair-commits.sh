#!/usr/bin/env bash
# Usage: pair-commits.sh <commit A> <commit B> <case>...
#
# Times the same case files under two commits of the emitter, alternating the arms on one runner so
# the comparison is not between machines. The order is A B B A, so neither arm always runs on a
# cold cache and neither always runs first. Only `PrimeCert/SegmentedSieve.lean` is taken from the
# commit under test; the case files and this script stay as the branch has them, so both arms run
# the same inputs through different emitters.
#
# Each arm's output carries TAG=A- or TAG=B-, so `run.sh`'s per-case files do not overwrite each
# other and the reported lines say which arm they belong to.
set +e +o pipefail
A=$1
B=$2
shift 2
cases=("$@")

arm() {
  local tag=$1
  local commit=$2
  git checkout -q "$commit" -- PrimeCert/SegmentedSieve.lean
  lake build PrimeCert.SegmentedSieve > /dev/null 2>&1
  TAG="$tag-" LEAN_FLAGS=-DElab.async=false PrimeCertTest/SegTune/run.sh 1 "${cases[@]}"
}

for order in "A $A" "B $B" "B $B" "A $A"; do
  set -- $order
  arm "$1" "$2"
done

git checkout -q HEAD -- PrimeCert/SegmentedSieve.lean
