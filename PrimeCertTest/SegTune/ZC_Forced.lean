/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same band with a record's shared quantities named by value

The other arm of the pair described in `ZB_Record`. Mode 67 states the same literals through
`stripeBatchFK`, where the record's position, the divisor it names and its seed each pass through
`forceK`, whose `Nat.rec` evaluates them before the body sees them. A divisor's eight records then
present one value rather than eight copies of the term computing it.

A disagreement of a single bit would fail the kernel check and turn the run red, so a green pair
also says the two agree. -/

namespace PrimeCert.SegTune.ZC_Forced

run_sieve 10000000

run_segment_variant 67 100000000000001 4194304 333333 8192 10000000

end PrimeCert.SegTune.ZC_Forced
