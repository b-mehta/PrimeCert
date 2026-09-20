/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # One segment at a hundred billion, sorted

`H0_Sorted` a hundred times higher: 262144 positions from 100000000001, crossed out by the divisors
up to 316231, again just above the square root of the segment's top. The divisor bound grows with
the height while the segment's width does not, so a larger share of the divisors strike the segment
only a few times here than at ten billion. `H1_Marked` is the comparison arm. -/

namespace PrimeCert.SegTune.H1_Sorted

run_segment_variant 28 100000000001 262144 105410 1536

end PrimeCert.SegTune.H1_Sorted
