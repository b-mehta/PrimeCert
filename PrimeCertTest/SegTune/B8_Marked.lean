/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The three-and-four-strike band, marked the way the sieve does today

The comparison arm for `B9_Sorted`: the same divisors, the same batches, each marking the segment
once per divisor. -/

namespace PrimeCert.SegTune.B8_Marked

run_sieve 10000000

run_segment_variant 30 100000000000001 4194304 3333332 3072 10000000

end PrimeCert.SegTune.B8_Marked
