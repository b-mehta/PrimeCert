/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The three-and-four-strike band, sorted into slices

The divisors whose double fits inside the segment and whose quadruple does not, so each strikes
each of its two progressions at most twice. Their strikes are sorted into 65536-bit pieces of the
segment, four records to a divisor, with the record of which positions were accounted for and the
clear a run would then owe. `B8_Marked` is the same band marked the way the sieve does today, so
the pair is the change on its own. No chain and no final theorem in either, and no proof yet. -/

namespace PrimeCert.SegTune.B9_Sorted

run_sieve 10000000

run_segment_variant 29 100000000000001 4194304 3333332 3072 10000000

end PrimeCert.SegTune.B9_Sorted
