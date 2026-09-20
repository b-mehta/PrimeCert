/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same run with a ten times larger base sieve beside it

Two pairs with nearly the same divisor ratio gave 0.156 and 0.328, and the base sieve moved through
one of them and not the other. But holding the base at a million also forces the bound below a
million and so forces the many-strike regime, so that pair holds the base and the regime together
and cannot say which the factor of two belongs to.

This arm holds everything else. It is `C7_B1e6` exactly — same width, start, fuel, divisors, mix,
batch length and emitted statements — with the base sieve alone ten times larger. Near 1.0 against
it and the base is not in the measured residual; near 2.0 and it is. -/

namespace PrimeCert.SegTune.C7_Base1e7

run_sieve 10000000

run_segment_variant 20 100000000000001 4194304 333333 1536 10000000

end PrimeCert.SegTune.C7_Base1e7
