/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Harmonic timing case: bound `10 ^ 7`, split into 770 position classes

Builds the `10 ^ 7` sieve, then encloses the sum of the reciprocals of the primes up to `10 ^ 7`
with each fold split into the 770 residue classes of the position modulo 770 (the classes of the
number modulo 2310), each class cut into batches of 20480 positions. `Base1_Sieve1e7` runs the sieve
step alone, so the difference between the two files is the cost of the folds.
-/

namespace PrimeCert.Sieve

run_sieve 10000000

end PrimeCert.Sieve

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_classes 10000000 20 770 20480
