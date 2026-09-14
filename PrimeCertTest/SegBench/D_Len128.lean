/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.SegmentedSieve

/-! # Segment benchmark: batch length 128, offset `10^16 + 1`, window 1024, base `10^6`

The short end of slice D. Shorter batches than this are not available at `fuel = 333333`: the
chain proof term nests one `segLoopK_chain` per batch and the kernel refuses deep enough nesting.
See the note in `README.md`.
-/

namespace PrimeCert.SegBench.D_Len128

run_segment 10000000000000001 1024 333333 128

end PrimeCert.SegBench.D_Len128
