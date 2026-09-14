/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.SegmentedSieve

/-! # Segment benchmark: window 16384, offset `10^16 + 1`, base `10^6` -/

namespace PrimeCert.SegBench.A_W16384

run_segment 10000000000000001 16384 333333 512

end PrimeCert.SegBench.A_W16384
