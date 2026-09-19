/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # One segment at a hundred billion, marked the way the sieve does today

The comparison arm for `H1_Sorted`. -/

namespace PrimeCert.SegTune.H1_Marked

run_sieve 1000000

run_segment_variant 20 100000000001 262144 105410 1536 1000000

end PrimeCert.SegTune.H1_Marked
