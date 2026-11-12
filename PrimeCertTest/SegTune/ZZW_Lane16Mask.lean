/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same octave, marked the way the sieve marks it today

Mode 79 over the band where a divisor's eightfold fits the window and its sixteenfold does not,
each divisor given a mask built by doubling. This is the arm `ZZV_Lane16` is measured against, and
it takes the same batch length so that the two run over the same divisors in the same groups.

Run the two alternated on one machine and compare kernel seconds. -/

namespace PrimeCert.SegTune.ZZW_Lane16Mask

run_sieve 10000000

run_segment_variant 79 100000000000001 4194304 333333 4096 10000000

end PrimeCert.SegTune.ZZW_Lane16Mask
