/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The eight-strike band, sorted into slices

The divisors whose quadruple fits inside the segment and whose octuple does not, so each strikes
each of its two progressions at most four times and eight records name every strike. This is the
octave below the band that `B9_Sorted` covers, and it holds 47 percent of the divisors that the
sorting leaves untouched today. `E8_Marked` is the same band marked the way the sieve does today.
No chain, no final theorem and no proof yet: this decides whether the band earns them. -/

namespace PrimeCert.SegTune.E9_Sorted

run_sieve 10000000

run_segment_variant 34 100000000000001 4194304 3333332 3072 10000000

end PrimeCert.SegTune.E9_Sorted
