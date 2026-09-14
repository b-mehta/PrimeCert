/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Harmonic timing case: bound `10 ^ 7`

Measures a `10 ^ 7` sieve followed by the two reciprocal folds over the 3333332 mod-6 wheel
positions up to `10 ^ 7`, at scale `10 ^ 20`, in batches of 20480 positions, so 163 batches per
fold. No cached sieve reaches `10 ^ 7`, so the sieve is built here; `Base1_Sieve1e7` runs that
step alone, and the difference between the two files is the cost of the folds.
-/

namespace PrimeCert.Sieve

run_sieve 10000000

end PrimeCert.Sieve

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic 10000000 20 20480
