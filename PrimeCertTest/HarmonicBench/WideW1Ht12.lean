/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt12

/-! # A window of 262144 positions at `10 ^ 12`, crossing off by divisors to 1999997

The baseline for the width comparison. `WideW2Ht12` and `WideW4Ht12` cover twice and four times as
many positions from the same start with the same divisors, so the three divide their cost by a
different number of candidates. Divisors reach 1999997 rather than the 1000001 of `Ht12`, because
a window may not reach the square of its largest divisor and four times the width would.
-/

namespace PrimeCert.WideW1Ht12

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000000001 262144 1999997 20 2048 1536 1 1

end PrimeCert.WideW1Ht12
