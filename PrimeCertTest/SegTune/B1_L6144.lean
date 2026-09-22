/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same segment in batches of 6144 positions

The long end of the series described in `B1_L1536`. -/

namespace PrimeCert.SegTune.B1_L6144

run_sieve 10000000

run_segment_variant 28 100000000000001 4194304 3333332 6144 10000000

end PrimeCert.SegTune.B1_L6144
