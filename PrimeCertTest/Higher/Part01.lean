/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The primes from `1156964609` to `1307959552` -/

namespace PrimeCert.Higher.P01

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1156964609 262144 53087 20 2048 1536 192 1

end PrimeCert.Higher.P01
