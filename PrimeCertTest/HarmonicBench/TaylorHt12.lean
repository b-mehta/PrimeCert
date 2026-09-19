/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt12

/-! # One window at `10 ^ 12` through the offset expansion

`Ht12` is the same window through the reciprocal fold, and is the arm to compare it with.
-/

namespace PrimeCert.TaylorHt12

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000000001 262144 1000001 20 2048 1536 1 8

end PrimeCert.TaylorHt12
