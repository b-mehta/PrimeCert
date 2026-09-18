/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public import PrimeCertTest.HarmonicBench.SieveHt12

/-! # Two windows above `10 ^ 12` (see `Shape.Part00`) -/

namespace PrimeCert.Shape.P05

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000007864321 262144 1000013 20 2048 1536 2 1

end PrimeCert.Shape.P05
