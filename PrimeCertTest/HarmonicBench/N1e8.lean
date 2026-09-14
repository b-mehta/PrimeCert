/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Harmonic timing case: bound `10 ^ 8`

Measures a `10 ^ 8` sieve followed by the two reciprocal folds over the 33333332 mod-6 wheel
positions up to `10 ^ 8`, at scale `10 ^ 20`, in batches of 20480 positions, so 1628 batches per
fold. No cached sieve reaches `10 ^ 8`, so the sieve is built here as
`PrimeCertTest.SieveVerify1e8` does; `Base2_Sieve1e8` runs that step alone, and the difference
between the two files is the cost of the folds.

This is the largest bound the unsegmented sieve reaches: its bitset is one numeral of 33333333
bits.
-/

namespace PrimeCert.Sieve

run_sieve 100000000

end PrimeCert.Sieve

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic 100000000 20 20480
