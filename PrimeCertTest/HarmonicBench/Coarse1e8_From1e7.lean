/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public import PrimeCertTest.HarmonicBench.SplitSieve1e8

/-! # Bound `10 ^ 8` at scale `10 ^ 12`, runs of equal quotient above ten million

Positions up to 3333333 (numbers up to ten million) are summed one at a time; above that the
quotient is constant over runs of about thirty positions or more, and each run costs one count of
set bits.
-/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_coarse 100000000 12 2048 3333333
