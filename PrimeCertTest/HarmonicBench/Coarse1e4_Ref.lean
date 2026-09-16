/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public import PrimeCertTest.HarmonicBench.SplitSieve1e4

/-! # Bound `10 ^ 4` at scale `10 ^ 4`, every position summed one at a time

The answer here must match `Coarse1e4`, which sums the top of the range in runs instead.
-/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_window 10000 4 256 0 2
