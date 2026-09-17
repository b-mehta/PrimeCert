/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The window sieve at 2097152 candidates

The midpoint between `N1M_M16` and `N4M_M16`, so the three together give the shape of the curve
below the ladder's smallest rung. -/

namespace PrimeCert.SegTune.N2M_M16

run_sieve 10000000

run_segment_variant 16 100000000000001 2097152 3333332 1536 10000000

end PrimeCert.SegTune.N2M_M16
