/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The double-width window, re-asked on the route we actually run

W = 8388608, which is 128 slices and covers 25165824 integers, against `ZZH_FullWindow28`'s
4194304 bits over 12582912. **One round of this covers two of that**, so every figure here is
halved before it is compared, and that is the only way to read it.

The width was measured on 2026-11-12 and settled at 4194304: doubling gave 3% less kernel and 7%
more processor per integer, at **1.9x the peak**, and 3% did not buy back half the packing. **That
was taken when the control peaked at 11.76 GB.** The sorted route has since brought the control to
**2.61 GB**, so the packing arithmetic that decided it no longer holds: the same 1.9x now lands
near 5 GB rather than near 22, and on a box with 32 vCPU and plenty of memory the cores bind rather
than the memory, in which case the peak buys nothing and the 3% is the whole of it.

So this re-asks a settled question on changed ground, rather than a new question. Pair with
`ZZH_FullWindow28`, both arms in one job, peak for each.

**Read throughput as windows per machine-hour from a measured marginal**, not from either arm's own
peak, and halve this arm's figures first. If it does not win per integer on processor as well as
kernel, the width stays where it is and this is closed for good rather than re-asked a third time.

Nothing here depends on the skip-set work; it shares only the control.

Throwaway. -/

namespace PrimeCert.SegTune.ZZS_WideWindow

run_sieve 10000000

run_segment_variant 28 100000000000001 8388608 3333333 8192 10000000

end PrimeCert.SegTune.ZZS_WideWindow
