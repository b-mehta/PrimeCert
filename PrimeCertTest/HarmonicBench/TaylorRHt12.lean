/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt12

/-! # The sums of the primes and their squares, with every numeral a raw literal

The enclosure of `TaylorHt12`, whose two summands are written as first drafted. Here both write
every numeral as a raw literal, and the square names its number once. `Ht12` is the arm using one
division per prime, which has had the same treatment.
-/

namespace PrimeCert.TaylorRHt12

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000000001 262144 1000001 20 2048 1536 1 12

end PrimeCert.TaylorRHt12
