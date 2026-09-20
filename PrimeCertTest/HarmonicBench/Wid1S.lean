/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt12

/-! # 786432 integers from `10 ^ 12`, crossed off with the strikes sorted

`Wid1Ht12` is the same segment crossed off by the graded batch length. The pair, and the three
pairs at twice, four times and eight times the width, say where the whole cost of a segment is
least once the summing is counted as well as the crossing off.
-/

namespace PrimeCert.Wid1S

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000000001 262144 1000007 20 2048 1536 1 1 28

end PrimeCert.Wid1S
