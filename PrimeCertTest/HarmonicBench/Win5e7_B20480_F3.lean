/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Bound `5 * 10 ^ 7`, windows of 20480 positions, packed fold

Every batch reads its own 20480-bit window of the sieve, each batch's link to the whole sieve is its
own declaration, and the chain over batches carries only literals. `Base4_Sieve5e7` runs the sieve
step alone.
-/

namespace PrimeCert.Sieve

run_sieve 50000000

end PrimeCert.Sieve

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_window 50000000 20 20480 0 3
