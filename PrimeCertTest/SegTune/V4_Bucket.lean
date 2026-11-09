/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The widest band's strikes joined a leaf at a time

`V3_Seed` adds the strike arithmetic without placing anything. This adds instead the batch's
strikes joined in leaf order, each leaf built whole and joined once, so against `V3_Seed` it
prices that grouping against the descent the tree performs for every strike. -/

namespace PrimeCert.SegTune.V4_Bucket

run_sieve 10000000

run_segment_variant 61 100000000000001 4194304 3333332 8192 10000000

end PrimeCert.SegTune.V4_Bucket
