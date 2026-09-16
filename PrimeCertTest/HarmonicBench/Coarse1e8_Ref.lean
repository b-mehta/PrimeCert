/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public import PrimeCertTest.HarmonicBench.SplitSieve1e8

/-! # Bound `10 ^ 8` at scale `10 ^ 12`, every position summed one at a time

The baseline for the two `Coarse1e8_*` cases: same bound, same scale, same window size, with no
runs of equal quotient. At this scale the enclosure is about six decimal places wide.
-/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_window 100000000 12 2048 0 3
