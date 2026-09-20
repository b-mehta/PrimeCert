/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # One segment at a trillion, 262144 positions, sorted

The first of four widths at a start of 1000000000001 with divisors to 1000003 throughout, so that
only the width moves. The quantity that decides whether sorting the strikes can pay is the ratio of
the divisor bound to the width in positions, which is about 3.8 here and falls to about 0.48 at the
widest of the four. Each width has a marked arm beside it. -/

namespace PrimeCert.SegTune.V262_Sorted

run_sieve 10000000

run_segment_variant 28 1000000000001 262144 333334 1536 10000000

end PrimeCert.SegTune.V262_Sorted
