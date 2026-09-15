/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Bound `5 * 10 ^ 7`, windows of 8192 positions, packed fold

As `Win5e7_B20480_F3` with smaller windows: 2035 batches instead of 814.
-/

namespace PrimeCert.Sieve

run_sieve 50000000

end PrimeCert.Sieve

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_window 50000000 20 8192 0 3
