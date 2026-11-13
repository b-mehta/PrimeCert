/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same four slices, stated over shorter ones

`ZZG_SkipSlices` keeps the 65536-bit slice the kernel refused and raises the recursion limit. This
takes the other route and shortens the slice to 4096, leaving the limit alone: 64 gcd equations
over this window in place of 4, each a sixteenth as deep.

**The slice size is not what the recursion limit answers to.** This failed at bs 4096 where
`ZZG_SkipSlices` passed at bs 65536, the two differing only in that `ZZG` raises the limit. So the
limit is raised here too, and what the short slice is for is memory, not depth: at bs 65536 the
full window reached 40 GB against the control's 2.61 and was killed before the kernel had done
much. A slice sets how large each live product is, so this is the shape left to try.

Throwaway. -/

namespace PrimeCert.SegTune.ZZK_SkipSlices4k

set_option maxRecDepth 1000000 in
run_segment_skip 100000000000001 262144 50000 1024 1024 4096 1000000

end PrimeCert.SegTune.ZZK_SkipSlices4k
