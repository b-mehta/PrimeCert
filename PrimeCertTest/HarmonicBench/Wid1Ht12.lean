/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt12

/-! # Interval length 786432 from `10 ^ 12`, sieved by the primes up to 1000007

The shortest of four intervals that share a start and a set of divisors. `Wid2Ht12`, `Wid4Ht12`
and `Wid8Ht12` are two, four and eight times as long. The divisor bound 1000007 is the least
wheel value above the square root of the top of the longest of the four, so all four are sieved
by the same primes and their costs divide by different numbers of integers.
-/

namespace PrimeCert.Wid1Ht12

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000000001 262144 1000007 20 2048 1536 1 1

end PrimeCert.Wid1Ht12
