/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public import PrimeCertTest.HarmonicBench.Split1e8W_P0
public import PrimeCertTest.HarmonicBench.Split1e8W_P1
public import PrimeCertTest.HarmonicBench.Split1e8W_P2
public import PrimeCertTest.HarmonicBench.Split1e8W_P3

/-! # The four quarters of the run to `10 ^ 8` with windows of 8192, joined -/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_merge 100000000 20 8192 4
