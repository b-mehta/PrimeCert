/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # What the sieve actually emits today

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
