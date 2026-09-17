/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The primes from `628482305` to `703979776` -/

namespace PrimeCert.Billion.P07

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 628482305 1048576 31721 20 2048 1536 24

end PrimeCert.Billion.P07
