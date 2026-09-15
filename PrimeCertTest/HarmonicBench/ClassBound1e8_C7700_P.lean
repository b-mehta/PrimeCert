/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Harmonic timing case: bound `10 ^ 8`, 7700 position classes, packed fold

7700 classes of 4329 positions each, every class a single batch, with the two folds packed into one.
-/

namespace PrimeCert.Sieve

run_sieve 100000000

end PrimeCert.Sieve

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_classes 100000000 20 7700 20480 3
