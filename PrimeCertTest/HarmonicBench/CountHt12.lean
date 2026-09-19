/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt12

/-! # One window at `10 ^ 12` from the count of its primes

Every prime the window covers lies between its first and last numbers, so the count on its own
gives an enclosure. This is the coarsest arm of the family and the one with a single fold.
-/

namespace PrimeCert.CountHt12

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000000001 262144 1000001 20 2048 1536 1 11

end PrimeCert.CountHt12
