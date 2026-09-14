/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.SegmentedSieve

/-! # Segment benchmark: batch length 256, offset `10^16 + 1`, window 1024, base `10^6` -/

namespace PrimeCert.SegBench.D_Len256

run_segment 10000000000000001 1024 333333 256

end PrimeCert.SegBench.D_Len256
