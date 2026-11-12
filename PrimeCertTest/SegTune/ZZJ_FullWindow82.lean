/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCertTest.LaneChain

/-! # The same window with one more band sorted

Mode 82 is mode 28 with the octave where a divisor's eightfold fits the window and its sixteenfold
does not sorted at sixteen records a divisor, rather than given a mask. Pair with
`ZZH_FullWindow28`, which is the same window on the route the sieve runs today.

Measured in isolation on 2026-11-12, that band alone came to kernel 22.59-22.88 s sorted against
25.95-26.25 masked (`ZZV_Lane16` against `ZZW_Lane16Mask`), so the gap to look for here is about
3.4 s of a window's 157 s of kernel, a little over 2%. That is small enough that it needs both
arms in one job to resolve: hosts vary by far more than that.

`PrimeCertTest.LaneChain` is imported because `stripeStepBand16` lives there; the emitter names
that import if it is missing. -/

namespace PrimeCert.SegTune.ZZJ_FullWindow82

run_sieve 10000000

run_segment_variant 82 100000000000001 4194304 3333333 8192 10000000

end PrimeCert.SegTune.ZZJ_FullWindow82
