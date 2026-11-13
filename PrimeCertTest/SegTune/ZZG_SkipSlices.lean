/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The skip set across more than one slice

`ZZF_SkipSmoke` runs on a 65536-bit window, which is exactly one slice, so it says nothing about
the per-slice offsets in the gcd equations. This window is four slices. An off-by-one in the
`k * bs` offset would state a gcd over the wrong stretch of the window, and the kernel settles that
by checking each literal.

**This case failed at `1251b3c`** with `(kernel) deep recursion detected`, at a slice of 65536
bits, which is the same slice size the one-slice case took without complaint. The emitter reached
the end and its self-check passed, so what the kernel refused is the gcd statement itself.
`prodLiveFromK` is a `Nat.rec` over the slice, so the slice size sets how deep that term goes, and
the slice is now an argument. This case keeps 65536 and raises the recursion limit, which is
goldbach's suggestion and the cheaper of the two to try; `ZZK_SkipSlices4k` instead shortens the
slice and leaves the limit alone. **Run both: whichever passes decides the shape the full window
is measured in.** If both pass, the short slice is the one to prefer, since it needs no option set.

Throwaway. -/

namespace PrimeCert.SegTune.ZZG_SkipSlices

set_option maxRecDepth 1000000 in
run_segment_skip 100000000000001 262144 50000 1024 1024 65536 1000000

end PrimeCert.SegTune.ZZG_SkipSlices
