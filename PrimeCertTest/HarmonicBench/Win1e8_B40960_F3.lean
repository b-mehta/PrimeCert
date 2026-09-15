/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Bound `10 ^ 8`, windows of 40960 positions, packed fold

Larger windows than `Win1e8_B20480_F3`, so fewer batches, each covering more positions.
-/

namespace PrimeCert.Sieve

run_sieve 100000000

end PrimeCert.Sieve

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_window 100000000 20 40960 0 3
