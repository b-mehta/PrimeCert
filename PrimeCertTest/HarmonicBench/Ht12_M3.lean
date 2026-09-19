/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt12

/-! # The whole window at `10 ^ 12` with the clamped loop reading slices

`Ht12` is the same window and the same sum, sieved by the loop that walks every base index and
builds a full mask for each prime. Timing the two apart shows what the loop is worth across a
whole window rather than across its sieving alone.
-/

namespace PrimeCert.Ht12_M3

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000000001 262144 1000001 20 2048 1536 1 1 3

end PrimeCert.Ht12_M3
