/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Harmonic timing case: bound `10 ^ 8`, 770 position classes, batches of 512

As `ClassBound1e8`, with each class cut into batches of 512 positions instead of 20480.
-/

namespace PrimeCert.Sieve

run_sieve 100000000

end PrimeCert.Sieve

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_classes 100000000 20 770 512
