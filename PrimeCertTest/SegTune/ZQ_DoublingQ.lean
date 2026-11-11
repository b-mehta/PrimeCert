/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The doubling mask at a quarter of the window

The cheap version of `ZG_Doubling`, for a shared machine. These modes mark every divisor with a
full mask rather than taking the sorted route a production window takes, so the full-size triple
costs more than a production window does and I could not bound it honestly. At a quarter of the
width with a quarter of the divisors the same question is asked for roughly a sixteenth of the
work, and the question is a ratio, so the smaller run answers it.

Pair with `ZR_ExactSpanQ` and `ZS_JoinedQ`. Run the full-size triple only if this one says the
answer is worth the slot. -/

namespace PrimeCert.SegTune.ZQ_DoublingQ

run_segment_variant 18 100000000000001 1048576 83333 8192

end PrimeCert.SegTune.ZQ_DoublingQ
