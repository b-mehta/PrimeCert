/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same band with one bit naming the strike

Mode 86: the same divisors as `ZZD_WideCtl31`, the same two records apiece, the same emitted
equations, differing in one thing. A divisor in this band has two strikes inside the window, so one
bit names them and fifteen are left for the position. The batch cap goes from 8192 to 32768, and
the same band is covered in 81 batches where the control takes 322.

No chain is proved, by design: the kernel still checks every literal, so the time is real, but
nothing here ties these batches back to the segment. The band-2 soundness argument gets written if
and only if this arm wins.

**Compare the batch lemma counts before reading any seconds.** 81 against 322 is what says the cap
actually moved; equal counts would mean the mode is inert, as 84 and 85 turned out to be.

Throwaway. -/

namespace PrimeCert.SegTune.ZZE_WideOne86

run_sieve 10000000

run_segment_variant 86 100000000000001 4194304 3333333 32768 10000000

end PrimeCert.SegTune.ZZE_WideOne86
