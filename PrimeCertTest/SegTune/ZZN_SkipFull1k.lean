/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The full window with the skip set, over 1024-bit slices

The third point, to be run **only if `ZZL_SkipFull4k` survives but stays above
`ZZH_FullWindow28`**, which would say the slice size is doing something and the bracket is worth
filling in. 4096 gcd equations over the window.

If `ZZL_SkipFull4k` runs away like `ZZI_SkipFull` did at 40 GB, this one does not get a box: two
slice sizes an order apart both running away settles it.

Throwaway. -/

namespace PrimeCert.SegTune.ZZN_SkipFull1k

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip 100000000000001 4194304 3333333 8192 0 1024 10000000

end PrimeCert.SegTune.ZZN_SkipFull1k
