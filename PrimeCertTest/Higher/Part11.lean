/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The primes from `2666914049` to `2817908992`

The last of the twelve, so it carries the range past `2.8 * 10 ^ 9`.
-/

namespace PrimeCert.Higher.P11

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 2666914049 262144 53087 20 2048 1536 192 1

end PrimeCert.Higher.P11
