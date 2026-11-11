/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Every batch 128 positions long

The lower bracket of the pair described in `ZZL_Uniform256`. Shorter batches mean more of them,
each with its own chain step and its own window-sized literal kept for the file's life, so the
peak cannot fall forever: somewhere below here the literals outweigh what the shorter batch saves.
This is to find whether that turn has already happened by 128. -/

namespace PrimeCert.SegTune.ZZM_Uniform128

run_sieve 10000000

run_segment_variant 73 100000000000001 4194304 333333 128 10000000

end PrimeCert.SegTune.ZZM_Uniform128
