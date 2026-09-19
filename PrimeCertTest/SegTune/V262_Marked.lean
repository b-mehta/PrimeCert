/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # One segment at a trillion, 262144 positions, marked

The comparison arm for `V262_Sorted`. -/

namespace PrimeCert.SegTune.V262_Marked

run_sieve 10000000

run_segment_variant 20 1000000000001 262144 333334 1536 10000000

end PrimeCert.SegTune.V262_Marked
