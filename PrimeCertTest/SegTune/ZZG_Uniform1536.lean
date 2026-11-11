/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Every batch 1536 positions long

The other uniform point described in `ZZF_Uniform512`, at twice the schedule's largest value, so
the pair brackets the schedule from both sides rather than only from below. -/

namespace PrimeCert.SegTune.ZZG_Uniform1536

run_sieve 10000000

run_segment_variant 73 100000000000001 4194304 333333 1536 10000000

end PrimeCert.SegTune.ZZG_Uniform1536
