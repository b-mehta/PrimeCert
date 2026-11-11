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
period, which leaves the bits inside the window where they are. Simulated over a spread of
divisors, the mask averages 0.637 of the width the doubling leaves.

The kernel works out the round count and the final shift itself, from the divisor and the window,
in operations it reduces directly, so this arm carries no literals the other does not. -/

namespace PrimeCert.SegTune.ZH_ExactSpan

run_sieve 10000000

run_segment_variant 69 100000000000001 4194304 333333 8192 10000000

end PrimeCert.SegTune.ZH_ExactSpan
