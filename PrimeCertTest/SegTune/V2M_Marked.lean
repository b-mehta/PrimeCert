/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # One segment at a trillion, 2097152 positions, marked

The comparison arm for `V2M_Sorted`. -/

namespace PrimeCert.SegTune.V2M_Marked

run_sieve 10000000

run_segment_variant 20 1000000000001 2097152 333334 1536 10000000

end PrimeCert.SegTune.V2M_Marked
