/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same segment in batches of 1536 positions

`B1_L1536`, `E2_Rec2` and `B1_L6144` hold the window at 4194304 bits and the divisors at 10^7, and
vary only how many positions a batch covers. The batch count moves with that; the width of each
batch's assembled mask does not. The columns to read are `addDecl` against the rest of
`Elab.command`. -/

namespace PrimeCert.SegTune.B1_L1536

run_sieve 10000000

run_segment_variant 28 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.B1_L1536
