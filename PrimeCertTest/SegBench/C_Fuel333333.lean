/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.SegmentedSieve

/-! # Segment benchmark: base numbers to `10^6`, offset `10^16 + 1`, window 1024

The shared corner of slices A, B, C and D; see `B_Off16`.
-/

namespace PrimeCert.SegBench.C_Fuel333333

run_segment 10000000000000001 1024 333333 512

end PrimeCert.SegBench.C_Fuel333333
