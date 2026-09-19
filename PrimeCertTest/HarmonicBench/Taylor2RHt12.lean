/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt12

/-! # Two folds, the count and the sum of the primes, with every numeral a raw literal

The sum of the squares is bounded by the last number of the range times the sum of the primes, so
only two quantities are folded. The summand giving the prime at a position writes every numeral as
a bare `Nat` constant.
-/

namespace PrimeCert.Taylor2RHt12

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000000001 262144 1000001 20 2048 1536 1 13

end PrimeCert.Taylor2RHt12
