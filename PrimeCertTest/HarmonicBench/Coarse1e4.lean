/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public import PrimeCertTest.HarmonicBench.SplitSieve1e4

/-! # Bound `10 ^ 4` at scale `10 ^ 4`, the top of the range summed in runs

At this scale the quotient is constant over runs of positions above the crossover, so those
positions cost one count of set bits each run. `Split1e4_Ref` sums every position one at a time.
-/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_coarse 10000 4 256 400
