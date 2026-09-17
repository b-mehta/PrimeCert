/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # A quarter of a billion part, with a batch fold that carries a start and a step

24 windows of 262144 wheel positions from `100000001`, sieved by the primes up to `31721` and summed
at scale `10 ^ 20`, with the batch statements in raw literals. `Fold1e8_F2` is the same stretch with
the step-free batch fold, so the two together time that fold at the size the billion runs at.
-/

namespace PrimeCert.Fold1e8.F1

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 100000001 262144 31721 20 2048 1536 24 1

end PrimeCert.Fold1e8.F1
