/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public import PrimeCertTest.HarmonicBench.SplitSieve1e4

/-! # The run to `10 ^ 4` in one file, to compare with the split one -/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_window 10000 12 2048 0 3
