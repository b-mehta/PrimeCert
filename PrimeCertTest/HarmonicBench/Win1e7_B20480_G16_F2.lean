/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Window A/B case: bound `10 ^ 7`, windows of 20480 positions, segments of 16, two folds

Builds the `10 ^ 7` sieve first; `Base1_Sieve1e7` runs that step alone.
-/

namespace PrimeCert.Sieve

run_sieve 10000000

end PrimeCert.Sieve

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_window 10000000 20 20480 16 2
