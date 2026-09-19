/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The divisors past half the segment, with four records apiece

`Q9_Cleared` gives each of those divisors two records, one per progression, which is all their
strikes. This file gives them four, the extra pair stepping on by a further double and so always
landing past the end of the segment. That is what one family of definitions covering both bands
would cost, against `Q9_Cleared` as the two-record arm. -/

namespace PrimeCert.SegTune.Q9_Four

run_sieve 10000000

run_segment_variant 31 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.Q9_Four
