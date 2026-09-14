/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.SegmentedSieve

/-! # Segment benchmark: offset `10^18 + 1`, window 1024, base `10^6` -/

namespace PrimeCert.SegBench.B_Off18

run_segment 1000000000000000001 1024 333333 512

end PrimeCert.SegBench.B_Off18
