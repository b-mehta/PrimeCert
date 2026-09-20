/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # One segment at a trillion, 524288 positions, sorted

The second of the four widths. See `V262_Sorted` for what the sweep asks. -/

namespace PrimeCert.SegTune.V524_Sorted

run_sieve 10000000

run_segment_variant 28 1000000000001 524288 333334 1536 10000000

end PrimeCert.SegTune.V524_Sorted
