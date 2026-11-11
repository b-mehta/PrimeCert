/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same band with only the records that land inside the window

The other arm of the pair described in `ZU_AllRecords`, and a screen rather than a candidate.

**This mode is not sound and must not be landed.** What stops a divisor being skipped is that the
tally accounts for every strike of every divisor; mode 71 accounts only for the strikes inside the
window, so a divisor whose records were all dropped would pass unnoticed. It states a different
literal from `ZU_AllRecords` for that reason, and the two cannot be checked against each other.

It exists to put a number on the ceiling: 28.6 percent of that band's records name a strike past
the window, and the band is about 36 percent of a window's kernel time, so the ceiling is near 9
percent. If the measured gap is well under that, the sound version is not worth designing. -/

namespace PrimeCert.SegTune.ZV_WindowRecords

-- As in `ZU_AllRecords`: the band's divisors run past the default sieve's million.
run_sieve 10000000

run_segment_variant 71 100000000000001 4194304 333333 8192 10000000

end PrimeCert.SegTune.ZV_WindowRecords
