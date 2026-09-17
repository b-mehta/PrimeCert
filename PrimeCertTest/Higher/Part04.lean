/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The primes from `1609949441` to `1760944384` -/

namespace PrimeCert.Higher.P04

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1609949441 262144 53087 20 2048 1536 192 1

end PrimeCert.Higher.P04
