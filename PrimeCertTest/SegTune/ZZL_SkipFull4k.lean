/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The full window with the skip set, stated over 4096-bit slices

`ZZI_SkipFull` at a 4096-bit slice: 1024 gcd equations over the window in place of 64, each a
sixteenth as deep. Which of the two the kernel accepts is what `ZZG_SkipSlices` and
`ZZK_SkipSlices4k` settle; run whichever of this and `ZZI_SkipFull` matches the one that passed,
and if both passed, run both, because the slice size trades the number of gcd equations against
the depth of each and nothing measured says which way that goes.

Everything else is `ZZI_SkipFull`: pair with `ZZH_FullWindow28`, both arms in one job, peak for
each, and read the `skipGcd_` row apart from the batch lemmas.

Throwaway. -/

namespace PrimeCert.SegTune.ZZL_SkipFull4k

run_sieve 10000000

run_segment_skip 100000000000001 4194304 3333333 8192 32768 4096 10000000

end PrimeCert.SegTune.ZZL_SkipFull4k
