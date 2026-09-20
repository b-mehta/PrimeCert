/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The whole segment with the widest band walked by the kernel

`E2_Rec2` with the divisors whose double already passes the end of the segment routed through
`treeStep2`: the kernel derives each one's two strikes and dispatches them by the bits of the leaf
number, so the batch owes one equation rather than a record list, a tally and a clear. The other
two bands are unchanged, so the pair isolates that swap over a real segment. -/

namespace PrimeCert.SegTune.E2_Tree2

run_sieve 10000000

run_segment_variant 45 100000000000001 4194304 3333332 3072 10000000

end PrimeCert.SegTune.E2_Tree2
