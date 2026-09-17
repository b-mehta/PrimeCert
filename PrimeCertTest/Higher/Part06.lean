/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The primes from `1911939329` to `2062934272` -/

namespace PrimeCert.Higher.P06

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1911939329 262144 53087 20 2048 1536 192 1

end PrimeCert.Higher.P06
