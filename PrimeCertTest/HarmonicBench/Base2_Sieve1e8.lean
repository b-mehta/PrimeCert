/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Harmonic benchmark baseline: the `10 ^ 8` sieve

Measures `Base0_Startup` plus the sieve that the `10 ^ 8` case needs, and nothing else, so that
`N1e8` minus this file is the cost of the reciprocal folds rather than of the sieve under them.
-/

namespace PrimeCert.Sieve

run_sieve 100000000

end PrimeCert.Sieve
