/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The ceiling again, with the strike set taken from the wide band alone

`parts 10`, which is `parts 2` plus 8: the marking route over the marked subset, no gcds, and the
strike set swept from the wide band instead of a plain pass over every divisor.

`ZZP_SkipRouteOnly` measured the ceiling at **41% less kernel**, 88.8-91.2 s against 151.8-155.4 s,
and **+68% processor**, every bit of which was the 124 s plain marking pass. This replaces that
pass. The three lower bands are marked whether they strike or not, which gives up 61905 of the
497131 skips and keeps 435226, because 8459746 of the 10030004 strike records are the masked small
band and only 8.3% of it is skippable.

So the kernel figure should come out a little worse than `ZZP`'s, since fewer divisors are skipped,
and the processor figure is the question. **Pair with `ZZH_FullWindow28`, one job, peak each**, and
read the emitter's own lines: `lower bands batch …`, `wide sweep done … struck … of …`, and
`wide marking done`.

The sweep's counts are predicted: **struck 73742 of 508968 wide divisors**, and the marked set as
a whole should be **73742 plus every non-wide divisor**. Counted two ways, in the loop's order and
against a fixed window, both giving 73742, so a different number here means the sweep is wrong
rather than that the prediction was.

Throwaway. -/

namespace PrimeCert.SegTune.ZZU_WideSweep

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 10 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZU_WideSweep
