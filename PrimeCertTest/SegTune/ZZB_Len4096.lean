/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same records at the shorter batch length

Second of the three arms described in `ZZA_Len8192`: every record kept, as there, but batches of
4096 positions. This is the control for the batch length alone, which the flagged record forces
and which a sweep had settled at 8192. -/

namespace PrimeCert.SegTune.ZZB_Len4096

run_sieve 10000000

run_segment_variant 34 100000000000001 4194304 333333 4096 10000000

end PrimeCert.SegTune.ZZB_Len4096
