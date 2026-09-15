/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Harmonic timing baseline: the `5 * 10 ^ 7` sieve alone

The sieve step of `ClassBound5e7` with no fold, so the difference between the two files is the cost
of the folds.
-/

namespace PrimeCert.Sieve

run_sieve 50000000

end PrimeCert.Sieve
