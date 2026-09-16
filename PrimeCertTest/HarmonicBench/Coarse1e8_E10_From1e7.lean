/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public import PrimeCertTest.HarmonicBench.SplitSieve1e8

/-! # Bound `10 ^ 8` at scale `10 ^ 10`, runs of equal quotient above ten million

At this scale there are only about nine hundred runs above ten million, each thousands of positions
long, which is the setting where counting a run should beat dividing each of its positions.
-/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_coarse 100000000 10 2048 3333333
