/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The wide sweep with the self-check switched off

`parts 13`, which is `parts 5` plus 8: the marking route over the marked subset, no gcds, the
strike set swept from the wide band, and **no self-check**.

`ZZU_WideSweep` came back at 31% less kernel, 112.1-113.6 s against 162.9-164.9, with the wide
band's own row falling from 66.4-67.1 s to 16.0. Its processor was +59%, and the phase log puts
**80,042 ms of that in the self-check**, which rebuilds the window from the marked subset to prove
the skip set right. Production would never run it: the small cases establish the skip set, the
kernel checks every literal emitted, and `ZZU` already reported `agree true` on this very window.

So this is the same arm with that 80 s removed, and it is the honest figure to compare against
`ZZH_FullWindow28`. Everything else is `ZZU`: pair with `ZZH`, one job, peak each.

What remains after this is the marking pass, 80,404 ms, which is the three lower bands marked
plainly so the sweep has a window to test against. That is the next thing to attack, and
`scripts/wide_base_prefix.py` counts how shallow that base could be.

**The cross-checks should be unchanged**: struck 73742 of 508968, skipped 435226. `agree` is no
longer reported, since nothing is checked.

Throwaway. -/

namespace PrimeCert.SegTune.ZZV_WideSweepNoCheck

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 13 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZV_WideSweepNoCheck
