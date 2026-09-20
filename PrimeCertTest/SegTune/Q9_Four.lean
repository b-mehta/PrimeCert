/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The divisors past half the segment, under the wider record layout

`Q9_Cleared` gives each of those divisors two records, one per progression, in a layout whose
record spends one bit saying which progression. This file writes the same two records in the layout
the three-and-four-strike band needs, whose record spends two bits there. So the pair says what one
family of definitions covering both bands would cost. -/

namespace PrimeCert.SegTune.Q9_Four

run_sieve 10000000

run_segment_variant 31 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.Q9_Four
