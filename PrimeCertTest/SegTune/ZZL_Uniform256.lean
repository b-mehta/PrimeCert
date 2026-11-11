/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Every batch 256 positions long

Measured upward, peak memory tracks the batch length: uniform 512 peaks at 5.1-5.7 GB, 768 at
6.1-7.5, 1024 at 6.6-9.1, 1536 at 6.0-10.6, against the graded schedule's 4.4-5.5. Since a run
packs windows onto a machine, the peak decides how many fit, and the schedule beats every longer
uniform length on windows per machine-hour by about twofold on a 14 GB runner.

That argues for looking the other way. If 256 drops the peak to around 3.5 GB a 14 GB runner holds
four windows where the schedule holds two, which would be worth more than the few percent of extra
time shorter batches cost. This is the lower bracket; `ZZM_Uniform128` is the one below it.

Read the peak first and the seconds second. -/

namespace PrimeCert.SegTune.ZZL_Uniform256

run_sieve 10000000

run_segment_variant 73 100000000000001 4194304 333333 256 10000000

end PrimeCert.SegTune.ZZL_Uniform256
