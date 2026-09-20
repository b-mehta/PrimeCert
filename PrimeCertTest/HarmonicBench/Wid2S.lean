/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt12

/-! # 1572864 integers from `10 ^ 12`, crossed off with the strikes sorted (see `Wid1S`) -/

namespace PrimeCert.Wid2S

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000000001 524288 1000007 20 2048 1536 1 1 28

end PrimeCert.Wid2S
