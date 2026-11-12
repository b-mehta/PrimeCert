/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same window with one batch length a band

Mode 85 keeps `batchLen`'s four lengths and moves its boundaries onto the band edges. No proof is
involved; it is where the schedule changes gear, not what gear it changes to.

**The boundaries have never been varied, only the values, and they do not line up with the bands.**
At a 4194304 window the bands break at `index (Wm1 / 8)`, `index (Wm1 / 4)` and `index (Wm1 / 2)`,
which is 174762, 349524 and 699050; the schedule breaks at 20000, 300000 and 700000. Only the last
pair nearly agree. So today the masked band spans the 256 and 512 tiers, the eight-record band
spans 512 and 768, and **no band is given a single length** — which is what tuning one band at a
time quietly assumes it has. Modes 57 and 83 were both doing exactly that.

Pair with `ZZH_FullWindow28`, both arms in one job, peak for each. Read on windows per machine-hour
with a measured marginal, as `ZZO_FullWindow83` sets out. -/

namespace PrimeCert.SegTune.ZZY_FullWindow85

run_sieve 10000000

run_segment_variant 85 100000000000001 4194304 3333333 8192 10000000

end PrimeCert.SegTune.ZZY_FullWindow85
