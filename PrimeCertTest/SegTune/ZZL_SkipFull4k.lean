/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The full window with the skip set, over 4096-bit slices

`ZZI_SkipFull` at bs 65536 reached **40.0-40.3 GB** and was killed in all three rounds, against
the control's 2.61 GB, with kernel total 0.37 s at the kill, so it died before the kernel had done
much. This is the same window at bs 4096: 1024 gcd equations in place of 64, each over a slice a
sixteenth the size.

The slice sets how large one live product is, which is the only lever on this that does not change
the design, so this says whether the shape is salvageable or finished. Run it against
`ZZH_FullWindow28`, one job, peak for each. **If this also runs away, the gcd certificate is
rejected on memory and should not be tried again at another slice size** — 4096 against 65536 is a
wide enough bracket that a third point in between is not worth a box.

`ZZN_SkipFull1k` takes it one step further, to bs 1024. Run that only if this one survives but
stays above the control, which would say the slice is doing something and the bracket needs a
third point after all.

The recursion limit is raised because `ZZK_SkipSlices4k` showed the slice size is not what the
limit answers to.

Throwaway. -/

namespace PrimeCert.SegTune.ZZL_SkipFull4k

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip 100000000000001 4194304 3333333 8192 0 4096 10000000

end PrimeCert.SegTune.ZZL_SkipFull4k
