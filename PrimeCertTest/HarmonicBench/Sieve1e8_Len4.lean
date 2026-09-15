/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Window A/B case: the `10 ^ 8` sieve alone, with 4 sieving steps per batch

The same sieve as `Base2_Sieve1e8`, whose batches hold the default 16 sieving steps.
-/

namespace PrimeCert.Sieve

run_sieve 100000000 4

end PrimeCert.Sieve
