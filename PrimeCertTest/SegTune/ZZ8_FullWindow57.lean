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

It also bears on why `ZZJ_FullWindow82` lost: the sixteen-record octave was ahead of its mask at
batch length 4096 and behind it at the schedule's 512, and 4096 over the middle bands is exactly
what this mode gives. If this wins, mode 82 is worth asking again on top of it. -/

namespace PrimeCert.SegTune.ZZ8_FullWindow57

run_sieve 10000000

run_segment_variant 57 100000000000001 4194304 3333333 8192 10000000

end PrimeCert.SegTune.ZZ8_FullWindow57
