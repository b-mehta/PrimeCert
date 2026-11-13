/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same emitter-only run at a quarter of the window

`parts 6` at W = 1048576, 16 slices, against `ZZR_SkipEmitterOnly`'s 4194304 at 64. Same divisors,
same batch length, a quarter of the window.

The emitter completes at W = 65536 and dies at 40 GB at 4194304, so the failure is a matter of
scale and nobody has measured where in between it appears. This is one point in between. If the
peak comes back near a quarter of 40 GB, whatever is accumulating grows with the window and the
count of it is the same at both sizes; if it comes back small, there is a threshold somewhere above
this and the growth is not in the window.

A case file only, so it cannot break a build, and it is cheap: one round, read the peak and
`/tmp/skip-rss.log`.

Run it only if the fingerprint lines from `ZZR` at `0cf1f04` do not settle the cause outright,
which they may.

Throwaway. -/

namespace PrimeCert.SegTune.ZZT_SkipQuarter

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 6 100000000000001 1048576 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZT_SkipQuarter
