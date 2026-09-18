/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt12

/-! # `Ht12` with the denominator cut from `10 ^ 20` to `10 ^ 14`

The window and the folds are those of `Ht12`; each prime contributes the quotient of `10 ^ 14` by
itself rather than of `10 ^ 20`, and the enclosure is `10 ^ 6` times wider.
-/

namespace PrimeCert.Ht12_E14

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000000001 262144 1000001 14 2048 1536 1 1

end PrimeCert.Ht12_E14
