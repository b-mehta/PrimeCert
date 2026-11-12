/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Sorting one octave further down than the sieve sorts today

Mode 78 over the band where a divisor's eightfold fits the window and its sixteenfold does not.
Sixteen records name every strike of such a divisor, so the lane takes four bits of a record rather
than three and the position is left with twelve, which caps a batch at 4096 divisors.

Pair with `ZZW_Lane16Mask`, which is mode 79: the same divisors, marked by a mask the way the sieve
marks them today. The question the pair asks is whether the sorted route is still ahead an octave
below the band it covers now, where a divisor's mask is cheaper to build and its record count has
doubled.

Both state the same divisors, and mode 78's batch lemma is closed by reflection against what the
emitter sorted, so a green run also says the records decode the way they were packed.

**Measured 2026-11-12, and sorting wins on all three figures.** Fresh c7i.8xlarge, `run.sh 3`,
load about 1. Sorted: kernel 22.59-22.88 s, processor 24.3-24.6 s, peak 1.84 GB. Masked
(`ZZW_Lane16Mask`): kernel 25.95-26.25 s, processor 38.4-38.9 s, peak 5.28 GB. That is 13% less
kernel, 37% less processor and under four tenths of the peak.

**That verdict did not transfer, and the band was not landed.** Both arms here run at batch length
4096. Production reaches this band through the graded schedule, at 256 to 768, and measured there
(`ZZJ_FullWindow82` against `ZZH_FullWindow28`, both arms in one job at the full divisor set)
sorting the octave **loses** by about 3% of a window's kernel: the masked band falls 19.3 s and the
sorted band rises 23.5 s.

So read this pair as "sorting wins this band *at 4096*", which is true and useless, because no run
uses 4096 here. **A band comparison has to use the batch length the schedule actually gives that
band.** -/

namespace PrimeCert.SegTune.ZZV_Lane16

run_sieve 10000000

run_segment_variant 78 100000000000001 4194304 333333 4096 10000000

end PrimeCert.SegTune.ZZV_Lane16
