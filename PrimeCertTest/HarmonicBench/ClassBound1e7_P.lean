/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Harmonic timing case: bound `10 ^ 7`, 770 position classes, packed fold

As `ClassBound1e7`, with the reciprocal and count folds packed into one.
-/

namespace PrimeCert.Sieve

run_sieve 10000000

end PrimeCert.Sieve

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_classes 10000000 20 770 20480 3
