/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # A billion, 262144 positions, sorted

The height the prime reciprocal sum session's record runs at, where crossing off is 15 percent of a
segment and every divisor strikes it many times. Divisors to 31637. Against `N9_1M_S` at a width
four times greater, this says whether the preference for wide segments that showed at a trillion
reaches down here. -/

namespace PrimeCert.SegTune.N9_262_S

run_segment_variant 28 1000000001 262144 10545 1536

end PrimeCert.SegTune.N9_262_S
