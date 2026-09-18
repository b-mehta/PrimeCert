/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # One window at `10 ^ 15` (see `Ht09`)

The last height the stored sieve to `10 ^ 8` can serve with room to spare; at `10 ^ 16` the
divisors reach `100000001`.
-/

namespace PrimeCert.Ht15

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000000000001 262144 31622777 20 2048 1536 1 1

end PrimeCert.Ht15
