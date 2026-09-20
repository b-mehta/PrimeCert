/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same segment with the graded batch length and the sorted strikes

`A1_M20` with the divisors that strike the segment at most four times settled by sorting those
strikes into eight pieces of 65536 bits. -/

namespace PrimeCert.SegTune.A1_M28

run_segment_variant 28 1000000001 524288 33334 1536

end PrimeCert.SegTune.A1_M28
