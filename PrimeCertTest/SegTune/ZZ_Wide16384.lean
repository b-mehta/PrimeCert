/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The wide band in longer batches, which costs no new code

Mode 28 at `ZZH_FullWindow28`'s arguments but with the call's length at **16384** in place of 8192.
Below base index 700000 the schedule ignores the call and nothing changes; above it, which is the
band where a divisor strikes the window once or twice, the call is the batch length. So this one
argument varies that band alone.

**The direction comes from mode 83.** Taking the same band from 8192 down to 1536 cost 15% of
kernel, 17% of processor and 54% of peak, and raised the batch lemma count from 1469 to 2862 —
shorter batches there cost time *and* memory, because each batch leaves a window-sized literal
behind. Every other tier was tried and tied; this is the one that moved, and it moved a long way.
Whether 8192 is near the top of that curve or merely on it has never been asked.

Pair with `ZZH_FullWindow28`, both arms in one job, peak for each. If this wins, try 32768 before
believing it. -/

namespace PrimeCert.SegTune.ZZ_Wide16384

run_sieve 10000000

run_segment_variant 28 100000000000001 4194304 3333333 16384 10000000

end PrimeCert.SegTune.ZZ_Wide16384
