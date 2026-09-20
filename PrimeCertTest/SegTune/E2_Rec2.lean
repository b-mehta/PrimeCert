/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The whole segment as it stands, records in every band

The control for `E2_Tree2`. Every band is settled by sorting each divisor's strikes into records
and checking the batch against an assembled mask, a tally and a clear. -/

namespace PrimeCert.SegTune.E2_Rec2

run_sieve 10000000

run_segment_variant 28 100000000000001 4194304 3333332 3072 10000000

end PrimeCert.SegTune.E2_Rec2
