/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The primes from `326492417` to `401989888` -/

namespace PrimeCert.Billion.P03

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 326492417 262144 31627 20 2048 1536 96

end PrimeCert.Billion.P03
