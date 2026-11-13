/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The skip set taken from the marking pass, at no threshold

The same window as `ZZF_SkipSmoke`, with `thr` at 0. The striking set now comes from the marking
pass itself, which records whether each divisor cleared a bit, so there is no separate probe and
no prefix to define live against. Live is taken in the order the loop runs instead.

Two things to read. The marked count should be no worse than `ZZF_SkipSmoke`'s 4505 of 13677,
because marking in order clears more before each divisor is reached than a fixed prefix does. And
the emitter's `marking pass` line replaces what used to be a `test` line costing 688 ms here.

Throwaway. -/

namespace PrimeCert.SegTune.ZZM_SkipHits

run_segment_skip 100000000000001 65536 50000 1024 0 65536 1000000

end PrimeCert.SegTune.ZZM_SkipHits
