/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same band with the slices joined in pairs

A third arm beside `ZB_Record` and `ZC_Forced`, over the same band and the same divisors. Mode 68
states the literals through `stripeBatchJK`: the window's 64 slices are joined in pairs, doubling
the width as the join climbs, and the tally is carried as a small number and joined once at the
end. What it replaces shifts each finished slice into a number already as wide as the window and
folds the tally into that same number, so every slice touches the full width twice.

`ZB_Record` is the baseline for both this and `ZC_Forced`, so running the three together answers
both questions against one baseline on one machine. Nothing here is proved; the kernel checks the
literal, and a disagreement would turn the run red. -/

namespace PrimeCert.SegTune.ZE_Joined

run_sieve 10000000

run_segment_variant 68 100000000000001 4194304 333333 8192 10000000

end PrimeCert.SegTune.ZE_Joined
