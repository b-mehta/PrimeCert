/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public import PrimeCertTest.HarmonicBench.SplitSieve1e8

/-! # The first quarter of the run to `10 ^ 8`, a second time

The same work as `Split1e8_P0`, so that one quarter can be timed with nothing beside it and then
the quarters timed together, on one runner. It proves the same names, so it must never be imported
alongside `Split1e8_P0`.
-/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_part 100000000 20 2048 4 0
