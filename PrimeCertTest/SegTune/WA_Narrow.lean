/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # One window at the present width, sieved as a 1..10^12 run would be

Divisors to 10^6, which is what the topmost window of 1..10^12 needs. At this width the small
band reaches only p ≤ 524287, so the divisors above that fall in the eight-strike band, which is
13.7 percent of such a run. `WB_Wide` doubles the width, which pulls them all into the small
band; it covers twice the integers, so twice this window's cost is the comparison. -/

namespace PrimeCert.SegTune.WA_Narrow

run_sieve 10000000

run_segment_variant 28 100000000000001 4194304 333333 8192 10000000

end PrimeCert.SegTune.WA_Narrow
