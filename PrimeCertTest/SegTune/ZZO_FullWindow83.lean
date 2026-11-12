/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same window with the wide band in shorter batches

Mode 83 is mode 28 with `batchLenWide` in place of `batchLen`. The two schedules agree everywhere
but one tier: above base index 700000, which is the band where a divisor strikes the window once or
twice, `batchLenWide` gives **1536** where `batchLen` gives 3072. No proof is involved.

Pair with `ZZH_FullWindow28`. **That band is now the largest single share of a window's kernel**,
56.7-57.2 s of 146.6-147.6 at the full divisor set, and its batch length appears never to have been
measured: mode 21 already selects this schedule, but without the sorted route, so it cannot
separate the length from the route. This mode can.

Read it on windows per machine-hour, not seconds: halving a batch length cuts peak and adds
lemmas, and `ZZ8_FullWindow57` is the cautionary case — 8% less processor there was not worth 59%
more peak. So report peak for both arms. Both arms in one job on one box: three boxes of this
instance type ran the same file 30% apart.

**Measured 2026-11-12. Slower per window, and ahead per runner-hour — which way it goes depends on
the machine.** One job, fresh c7i.8xlarge, `run.sh 3`: kernel 155.6-158.9 s against mode 28's
150.4-154.6 (no overlap), processor 169.3-172.9 against 165.8-170.5 (overlapping), peak 2.37 GB
against 2.61. So **the band is about 7% slower and the window about 3%**.

A second run measured each mode's **marginal** cost on a shared box, which is what sets packing:

|         | 1 copy  | 4 copies | 7 copies | per copy      | wall at 7 copies |
| mode 28 | 1.84 GB | 7.26 GB  | 12.76 GB | 1.81-1.84 GB  | 182.7-185.4 s    |
| mode 83 | 1.60 GB | 6.37 GB  | 11.08 GB | 1.58-1.60 GB  | 182.9-185.4 s    |

The machine's cost a copy sits about 0.74 GB under the per-process peak in both modes, because the
shared oleans map once, and stays flat with concurrency. **Under load the two are level on wall**,
and mode 83 fits one more window per 14 GB runner — **14-17% more windows a runner-hour**.

**So it wins where memory binds and loses where cores do**, since on a 61 GiB box with 32 vCPU both
fit far more copies than there are cores and 83 is the slower of the two.

**Not landed**, because the runs this project makes are on 32-core AWS boxes, where cores bind and
the slower window simply loses. Kept, with its numbers, because the answer reverses on a 14 GB
runner, where it is worth 14-17% more windows an hour. If that is ever the target, measure the
runner's own base memory first: it decides whether the packing is 7 against 6 or 8 against 7. -/

namespace PrimeCert.SegTune.ZZO_FullWindow83

run_sieve 10000000

run_segment_variant 83 100000000000001 4194304 3333333 8192 10000000

end PrimeCert.SegTune.ZZO_FullWindow83
