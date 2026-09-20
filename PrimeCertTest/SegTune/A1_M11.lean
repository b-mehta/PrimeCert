/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # One segment at a billion, the shape the summing session ran before today

524288 positions from 1000000001 with divisors to 100003, the parameters the prime reciprocal sum
session measured at. This arm is the clamped loop reading the batch's own slice of the base sieve,
with a fixed batch length throughout. `A1_M20` adds the graded batch length, `A1_M28` adds the
sorted strikes on top of that, so the three together say which of the two changes earned the 9.6
percent that session saw. -/

namespace PrimeCert.SegTune.A1_M11

run_segment_variant 11 1000000001 524288 33334 1536

end PrimeCert.SegTune.A1_M11
