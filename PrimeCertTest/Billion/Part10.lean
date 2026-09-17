/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The primes from `854974721` to `930472192` -/

namespace PrimeCert.Billion.P10

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 854974721 1048576 31721 20 2048 1536 24

end PrimeCert.Billion.P10
