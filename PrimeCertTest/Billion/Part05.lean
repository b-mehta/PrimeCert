/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The primes from `477487361` to `552984832` -/

namespace PrimeCert.Billion.P05

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 477487361 262144 31721 20 2048 1536 96

end PrimeCert.Billion.P05
