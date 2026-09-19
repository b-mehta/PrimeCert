/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # One segment at ten billion, marked the way the sieve does today

The comparison arm for `H0_Sorted`: the same segment, the same divisors, each marking the whole
segment once. -/

namespace PrimeCert.SegTune.H0_Marked

run_sieve 1000000

run_segment_variant 20 10000000001 262144 33334 1536 1000000

end PrimeCert.SegTune.H0_Marked
