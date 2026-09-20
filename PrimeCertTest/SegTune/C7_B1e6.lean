/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same segment and shape with a tenth of the divisor bound

The emitter's common cost came out flattest per divisor across two parameter sets, but two points
cannot tell that apart from anything else scaling with the divisor count over the same range. This
is a third point taken by moving the bound alone: the same width, start and loop as `S7_Sched`,
with divisors to a million rather than ten million. -/

namespace PrimeCert.SegTune.C7_B1e6

run_sieve 1000000

run_segment_variant 20 100000000000001 4194304 333333 1536 1000000

end PrimeCert.SegTune.C7_B1e6
