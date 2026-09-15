/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public import PrimeCertTest.HarmonicBench.Split1e4_P0
public import PrimeCertTest.HarmonicBench.Split1e4_P1

/-! # The two halves of the run to `10 ^ 4`, joined -/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_merge 10000 12 2048 2
