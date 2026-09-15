/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public import PrimeCertTest.HarmonicBench.SplitSieve1e8

/-! # The first quarter of the run to `10 ^ 8` -/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_part 100000000 20 20480 4 0
