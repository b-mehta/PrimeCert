/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.SegmentedSieve

/-! # Segment benchmark: offset `10^16 + 1`, window 1024, base `10^6`

The shared corner of slices A, B, C and D. Identical to `A_W1024`, `C_Fuel333333` and a `len` of
512 in slice D; kept as its own file so each row of each slice has one file to time.
-/

namespace PrimeCert.SegBench.B_Off16

run_segment 10000000000000001 1024 333333 512

end PrimeCert.SegBench.B_Off16
