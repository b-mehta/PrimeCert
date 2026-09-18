/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt12

/-! # Twice the width of `WideW1Ht12`, same start and same divisors -/

namespace PrimeCert.WideW2Ht12

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000000001 524288 1999997 20 2048 1536 1 1

end PrimeCert.WideW2Ht12
