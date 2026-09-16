/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public import PrimeCertTest.HarmonicBench.SplitSieve1e8

/-! # Bound `10 ^ 8` at scale `10 ^ 12`, runs of equal quotient above thirty million

As `Coarse1e8_From1e7` with the crossover three times higher, so fewer positions are summed in runs
but each run is longer.
-/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_coarse 100000000 12 2048 10000000
