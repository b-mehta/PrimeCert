/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same window marked by masks built to its width

The other arm of the pair described in `ZG_Doubling`. Mode 69 stops the doubling one round before
it passes the window and finishes the span with a single shift by a multiple of the divisor's
period, which leaves the bits inside the window where they are. Over the divisors this window is
actually given, the spans total 0.762 of the doubling's, and 0.712 across the small band alone;
the mean span falls from 1.47 windows to 1.12, and the widest from 2.00 to 1.43. An earlier
figure of 0.637 came from a spread of divisors chosen by hand and flattered it.

The kernel works out the round count and the final shift itself, from the divisor and the window,
in operations it reduces directly, so this arm carries no literals the other does not. -/

namespace PrimeCert.SegTune.ZH_ExactSpan

run_sieve 10000000

run_segment_variant 69 100000000000001 4194304 333333 8192 10000000

end PrimeCert.SegTune.ZH_ExactSpan
