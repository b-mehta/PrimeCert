/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Bound `5 * 10 ^ 7` at scale `10 ^ 18`, two folds, windows of 20480 positions

The running total is about 2.9 times the scale, so at this scale it stays below `9.2 * 10 ^ 18`.
Compare `Win5e7_B20480_F2_E19`, where it does not.
-/

namespace PrimeCert.Sieve

run_sieve 50000000

end PrimeCert.Sieve

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_window 50000000 18 20480 0 2
