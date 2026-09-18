/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # One window at `10 ^ 9`

One of a series, `Ht09` to `Ht15`, each summing one window of 262144 positions just above `10 ^ e`
and sieved by the primes below the smallest wheel value whose square clears the window's top. The
series says what a window costs as a function of height, which is what an estimate for a large `N`
needs. `10 ^ 16` is the ceiling of the method: its divisors reach `100000001`, above the stored
sieve.
-/

namespace PrimeCert.Ht09

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 262144 31637 20 2048 1536 1 1

end PrimeCert.Ht09
