/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.SegmentedSieve

/-! # Segment benchmark: base numbers to `10^4`, offset `10^16 + 1`, window 1024 -/

namespace PrimeCert.SegBench.C_Fuel3333

run_segment 10000000000000001 1024 3333 512

end PrimeCert.SegBench.C_Fuel3333
