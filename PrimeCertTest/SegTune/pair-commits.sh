#!/usr/bin/env bash
# Usage: pair-commits.sh <commit A> <commit B> <case>...
#
# Times the same case files under two commits, alternating the arms on one runner so the comparison
# is not between machines. The order is A B B A, so neither arm always runs on a cold cache and
# neither always runs first. Only the paths in SWAP are taken from the commit under test, so the
# case files and this script stay as the branch has them and both arms run the same inputs.
# SWAP defaults to the emitter alone; set it to swap something else, such as the lakefile.
#
# Each arm's output carries TAG=A- or TAG=B-, so `run.sh`'s per-case files do not overwrite each
# other and the reported lines say which arm they belong to.
set +e +o pipefail
A=$1
B=$2
shift 2
cases=("$@")
read -r -a swap <<< "${SWAP:-PrimeCert/SegmentedSieve.lean}"

# RUNNER=pair times the cases together, two windows to a runner, which is the shape a real run
# uses; anything else times them one at a time through run.sh.
arm() {
  local tag=$1
  local commit=$2
  git checkout -q "$commit" -- "${swap[@]}"
  lake build PrimeCert.SegmentedSieve > /dev/null 2>&1
  if [ "${RUNNER:-run}" = "pair" ]; then
    echo "arm $tag"
    LEAN_FLAGS=-DElab.async=false PrimeCertTest/SegTune/pair.sh "${cases[@]}"
  else
    TAG="$tag-" LEAN_FLAGS=-DElab.async=false PrimeCertTest/SegTune/run.sh 1 "${cases[@]}"
  fi
}

for order in "A $A" "B $B" "B $B" "A $A"; do
  set -- $order
  arm "$1" "$2"
done

git checkout -q HEAD -- "${swap[@]}"
