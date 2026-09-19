/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The divisors below a quarter of the segment, marked the current way

`N7_M18` stops at wheel index 700416, covering every divisor whose multiples land in the segment
more than twice. This file stops at 349525, which is where a divisor's multiples start landing more
than four times. The difference between the two is what the divisors striking three or four times
cost, and those are the ones the sorting could be extended to. -/

namespace PrimeCert.SegTune.N7_M18b

run_sieve 10000000

run_segment_variant 18 100000000000001 4194304 349525 1536 10000000

end PrimeCert.SegTune.N7_M18b
