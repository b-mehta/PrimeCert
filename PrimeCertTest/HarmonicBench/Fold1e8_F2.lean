/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # A quarter of a billion part, with a step-free batch fold

The same 24 windows as `Fold1e8_F1`, summed with the batch fold that has no start to add and no step
to multiply by.
-/

namespace PrimeCert.Fold1e8.F2

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 100000001 262144 31721 20 2048 1536 24 2

end PrimeCert.Fold1e8.F2
