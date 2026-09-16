/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public import PrimeCertTest.HarmonicBench.SplitSieve1e8

/-! # Bound `10 ^ 8` at scale `10 ^ 10`, every position summed one at a time

The baseline for `Coarse1e8_E10_From1e7`. At this scale the enclosure is about three decimal places
wide, and runs of equal quotient are thousands of positions long near the top of the range.
-/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_window 100000000 10 2048 0 3
