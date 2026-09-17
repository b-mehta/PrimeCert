/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The primes from `1307959553` to `1458954496` -/

namespace PrimeCert.Higher.P02

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1307959553 262144 53087 20 2048 1536 192 1

end PrimeCert.Higher.P02
