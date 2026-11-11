/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Every batch 512 positions long

`WA_Narrow` is the schedule as it stands: `batchLen` gives 256 below base index 20000, 512 below
300000, 768 below 700000, and the call's length only above that. Those constants were set long
ago, and an earlier attempt to price them by varying the call's length measured nothing because
mode 28 never reads it at these fuels; every arm emitted the same 670 batch lemmas.

Mode 73 takes the length from the call for every batch, so a uniform length can be priced against
the schedule. This is the middle of the schedule's three values. Pair with `ZZG_Uniform1536` and
with `WA_Narrow`: if neither uniform length beats the schedule, the schedule is doing real work
and the constants can be left alone. -/

namespace PrimeCert.SegTune.ZZF_Uniform512

run_sieve 10000000

run_segment_variant 73 100000000000001 4194304 333333 512 10000000

end PrimeCert.SegTune.ZZF_Uniform512
