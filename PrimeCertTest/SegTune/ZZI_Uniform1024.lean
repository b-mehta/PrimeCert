/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Every batch 1024 positions long

Longer batches are faster and hungrier: against the schedule, uniform 1536 measured 7.1 percent
less processor time and 2.9 percent less kernel, with elaboration halved, but its peak went to
6.0-10.6 GB where the schedule sits at 4.4-5.5. That matters because a run packs several windows
onto one machine, so the peak a window reaches decides how many fit, and a 14 GB runner holding
two windows cannot take 10.6 GB each.

This is the midpoint, to find where the knee is. Read the peaks as carefully as the seconds; the
fastest length is not the right one if it halves how many windows a machine can hold. -/

namespace PrimeCert.SegTune.ZZI_Uniform1024

run_sieve 10000000

run_segment_variant 73 100000000000001 4194304 333333 1024 10000000

end PrimeCert.SegTune.ZZI_Uniform1024
