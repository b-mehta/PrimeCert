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
instance type ran the same file 30% apart. -/

namespace PrimeCert.SegTune.ZZO_FullWindow83

run_sieve 10000000

run_segment_variant 83 100000000000001 4194304 3333333 8192 10000000

end PrimeCert.SegTune.ZZO_FullWindow83
