/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # What the sieve emitted before 2026-11-12

**Superseded: `run_segment` now marks the clamped way, so this case no longer measures the
unclamped loop.** The arm that does is `run_segment_variant 0`. Kept for the record of the pair
that settled it: at `244790d`, fresh c7i.8xlarge, `run.sh 3`, load about 1, this case measured
kernel 89.40-89.61 s, window 134.4-134.7 s, processor 135.7-136.1 s, peak 1.89 GB, against
`ZZ2_ProdClamped`'s 85.98-86.76, 129.3-130.5, 130.6-131.9, 1.90 GB — **3.5% on both kernel and
processor, ranges not overlapping**, which is what moved the command.

The original description follows.

Plain `run_segment`, which is the command that produces a real window certificate. It marks
through `segMarkK`: a mask built with a fixed 32 doubling rounds, no dropping of seeds that fall
outside the window, no skipping the rounds for a divisor too large to repeat, and a subtraction
whether or not anything was hit.

Pair with `ZZ2_ProdClamped`, which is `run_segment_variant 9`: the same chain over the same
divisors, marking through `segMarkCK`, which does all four of those. `segLoopCK_eq_stride` already
proves the two loops equal, and the clamped route ends at the same `segEqI_` theorem about
`segRun`, so this is a change of emitter and not of statement.

Everything measured on this branch so far has been one variant against another. This pair asks the
question that decides whether any of it reaches the sieve: what the clamped marking is worth on the
production path. The batch length is passed explicitly and equal in both arms, since plain
`run_segment` uses one length for every batch and the graded schedule is not on this path either —
that is a separate gap, and holding the length fixed is what keeps this pair about clamping
alone. -/

namespace PrimeCert.SegTune.ZZ1_ProdPlain

run_sieve 10000000

run_segment 100000000000001 4194304 333333 512 10000000

end PrimeCert.SegTune.ZZ1_ProdPlain
