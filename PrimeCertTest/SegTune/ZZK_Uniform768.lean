/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Every batch 768 positions long

The lower point of the pair described in `ZZI_Uniform1024`, and the schedule's own largest value
made uniform. Between them they say where peak memory starts climbing away from the schedule's
4.4 to 5.5 GB, which is what decides how many windows a machine can hold at once. -/

namespace PrimeCert.SegTune.ZZK_Uniform768

run_sieve 10000000

run_segment_variant 73 100000000000001 4194304 333333 768 10000000

end PrimeCert.SegTune.ZZK_Uniform768
