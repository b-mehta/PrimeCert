/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same window with the batch's masks joined before clearing

A third arm beside `ZG_Doubling` and `ZH_ExactSpan`, over the same divisors. Mode 70 builds each
mask to the window's width as `ZH_ExactSpan` does, then joins the batch's masks into one and
clears the window once for the batch rather than once for each divisor.

Joining has been measured three times before and lost each time, always against masks built by
doubling, which span up to twice the window, so the join carried a number about as wide as what it
saved. Built to the window's width the join carries a narrower number, which is the condition
those three measurements never had. `ZG_Doubling` is the baseline for all three, so running them
together answers both questions on one baseline. -/

namespace PrimeCert.SegTune.ZI_Joined

run_sieve 10000000

run_segment_variant 70 100000000000001 4194304 333333 8192 10000000

end PrimeCert.SegTune.ZI_Joined
