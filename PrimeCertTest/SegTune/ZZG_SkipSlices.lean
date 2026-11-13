/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The skip set across more than one slice

`ZZF_SkipSmoke` runs on a 65536-bit window, which is exactly one slice, so it says nothing about
the per-slice offsets in the gcd equations. This window is four slices. An off-by-one in the
`k * 65536` offset would state a gcd over the wrong stretch of the window, and the kernel settles
that by checking each literal.

Throwaway. -/

namespace PrimeCert.SegTune.ZZG_SkipSlices

run_segment_skip 100000000000001 262144 50000 1024 1024 1000000

end PrimeCert.SegTune.ZZG_SkipSlices
