/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Window A/B case: bound `10 ^ 8`, windows of 20480 positions, segments of 64, one fold

Builds the `10 ^ 8` sieve first; `Base2_Sieve1e8` runs that step alone.
-/

namespace PrimeCert.Sieve

run_sieve 100000000

end PrimeCert.Sieve

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_window 100000000 20 20480 64 1
