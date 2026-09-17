/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The primes from `175497473` to `250994944` -/

namespace PrimeCert.Billion.P01

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 175497473 1048576 31721 20 2048 1536 24

end PrimeCert.Billion.P01
