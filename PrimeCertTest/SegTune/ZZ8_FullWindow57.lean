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
octave is settled anyway.

**Measured 2026-11-12. It buys time and spends memory, and that is why it never landed.** Both
arms in one job, fresh c7i.8xlarge, `run.sh 3`, ranges not overlapping:

|                     | mode 28       | mode 57       |
| kernel total        | 146.6-147.6 s | 136.8-137.7 s |
| sorted batch lemmas | 44.1-44.3     | 32.7-33.1     |
| processor           | 161.6-162.5 s | 148.6-149.7 s |
| peak                | 2.60-2.61 GB  | 4.15-4.16 GB  |
| batch lemma count   | 1469          | 832           |

**7% less kernel and 8% less processor, for 59% more peak**, the saving all in the sorted middle
band. Per machine-hour that is a loss where memory binds: a 14 GB runner holds five windows of
mode 28 against three of mode 57, so about **35% fewer windows a runner-hour**. Where cores bind
instead it is close, and which one binds depends on cores per copy, which is unmeasured above
eight concurrent.

**The 14.0% of 2026-11-07 was real and has not survived, because the baseline moved.** Mode 57's
peak then was 4.21 GB and is 4.15 now — unchanged. What changed is mode 28, which was 4.21 against
a uniform-8192 arm then and is 2.60 now, after the graded schedule and the asynchronous-check flag.
So mode 57 did not get worse; the default got leaner, and the trade stopped paying.

**Do not land it.** Reconsider only for a machine with memory to spare per core, and measure the
concurrency peak of mode 57 first — the 1.83 GB marginal in `scripts/fuel_by_window.py` is mode
28's and does not transfer. -/

namespace PrimeCert.SegTune.ZZ8_FullWindow57

run_sieve 10000000

run_segment_variant 57 100000000000001 4194304 3333333 8192 10000000

end PrimeCert.SegTune.ZZ8_FullWindow57
