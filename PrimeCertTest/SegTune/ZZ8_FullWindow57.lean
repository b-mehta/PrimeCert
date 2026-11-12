/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same window with the middle bands in longer batches

Mode 57 is mode 28 with `batchLenMid` in place of `batchLen`: 4096 over the two middle bands where
the default schedule gives 512, and 3072 above base index 700000 where it gives the call's length.
No proof is involved; it is a choice of how many divisors a batch holds.

Pair with `ZZH_FullWindow28`. **This was measured on 2026-11-07 at 14.0% less processor and 15.4%
less kernel than mode 28, three rounds of three with no overlap, and was never made the default.**
Those figures predate clamped marking and the banded route reaching `run_segment`, both of which
landed on 2026-11-12 and took a window from about 86 s of kernel to 161-163, so the gap has to be
re-measured against today's mode 28 rather than assumed to have survived.

**Read the pair on windows per machine-hour, not seconds per window.** Longer batches buy time and
cost peak memory, and a run packs windows onto a machine, so the figure that decides is
`min(RAM / peak, cores)` times the rate. That is what the batch-length sweep of 2026-11-11 settled,
and reading it the other way is what made an earlier uniform-length lead look real. Note that sweep
compared the graded schedule against *uniform* lengths and never tested `batchLenMid`, so this
pair is not a repeat of it. The 2026-11-07 run had mode 57 at a **lower** peak than its comparison
(2.73 GB against 4.21), but that comparison was uniform 8192, not today's default; `run.sh` reports
peak for both arms, so take it from there rather than from either of those.

This does not bear on `ZZJ_FullWindow82`. `batchLenMid`'s tiers break at base index 174762 and the
sixteen-record octave sits at 87381-174762, so it stays at 512 under this mode too, and that
octave is settled anyway. -/

namespace PrimeCert.SegTune.ZZ8_FullWindow57

run_sieve 10000000

run_segment_variant 57 100000000000001 4194304 3333333 8192 10000000

end PrimeCert.SegTune.ZZ8_FullWindow57
