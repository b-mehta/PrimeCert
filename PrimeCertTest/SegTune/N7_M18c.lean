/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The divisors below an eighth of the segment, marked the current way

`N7_M18b` stops at wheel index 349525, where a divisor's multiples start landing more than four
times. This file stops at 174762, where they start landing more than eight times. The difference
between the two is what the octave now sorted costs when it is marked instead. -/

namespace PrimeCert.SegTune.N7_M18c

run_sieve 10000000

run_segment_variant 18 100000000000001 4194304 174762 1536 10000000

end PrimeCert.SegTune.N7_M18c
