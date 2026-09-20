/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # One segment at a trillion, 2097152 positions, sorted

The widest of the four, where the ratio of divisor bound to width is about 0.48 and only the
divisors striking three or four times are left for the sorted route. -/

namespace PrimeCert.SegTune.V2M_Sorted

run_sieve 10000000

run_segment_variant 28 1000000000001 2097152 333334 1536 10000000

end PrimeCert.SegTune.V2M_Sorted
