/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # What the window's peak memory is actually made of

A window peaks at 4.4 to 5.5 GB, and that peak is what decides how many windows a machine can
hold, so it is worth more than any seconds left in the window. The batch length cannot move it:
measured from 128 up to 1536 the peak only goes 5.5, 4.9, 5.5, 7.5, 9.1, 10.6, so the floor near
4 to 5 GB is held by something else. The obvious candidates do not account for it either, since
670 window-sized literals are 343 MB and the ten million base sieve is 400 KB.

Mode 19 runs the same loop and emits one declaration at the end rather than one per batch, so its
peak is the loop's own footprint without the literals the other modes keep. Against `WA_Narrow`
at the same shape, the difference is what the kept declarations cost and the remainder is what the
reduction itself needs. Whichever of the two dominates is where a memory saving has to come from.

Pair with `WA_Narrow`. -/

namespace PrimeCert.SegTune.ZZN_LoopOnly

run_sieve 10000000

run_segment_variant 19 100000000000001 4194304 333333 8192 10000000

end PrimeCert.SegTune.ZZN_LoopOnly
