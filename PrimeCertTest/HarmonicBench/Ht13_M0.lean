/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt13

/-! # One window at `10 ^ 13`, crossed off by the loop in use until now

`Ht13_M11` is the same window through the clamped loop reading slices.
-/

namespace PrimeCert.Ht13_M0

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 10000000000001 262144 3162281 20 2048 1536 1 1 0

end PrimeCert.Ht13_M0
