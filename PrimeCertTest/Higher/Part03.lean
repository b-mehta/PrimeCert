/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The primes from `1458954497` to `1609949440` -/

namespace PrimeCert.Higher.P03

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1458954497 262144 53087 20 2048 1536 192 1

end PrimeCert.Higher.P03
