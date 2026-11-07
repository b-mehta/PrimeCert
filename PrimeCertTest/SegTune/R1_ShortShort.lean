/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The short middle tiers at the divisor count a window near 2.5e13 needs

A window is sound once every prime to the square root of its top is crossed, so one near 2.5e13
needs divisors to about 5e6, which is 1666666 wheel positions rather than 3333332. That reduces
the middle bands, and the question this pair answers is whether the 14 percent that batches of
4096 gave at the full divisor count survives when those bands are smaller.

`R1_ShortShort` keeps the 512 and 768 tiers, `R2_ShortLong` uses 4096. -/

namespace PrimeCert.SegTune.R1_ShortShort

run_sieve 10000000

run_segment_variant 28 100000000000001 4194304 1666666 8192 10000000

end PrimeCert.SegTune.R1_ShortShort
