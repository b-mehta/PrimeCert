/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Bound `5 * 10 ^ 7` at scale `10 ^ 14`, windows of 20480 positions, packed fold

As `Win5e7_B20480_F3` at a lower scale: the interval width is the number of contributing positions
over `10 ^ 14`, about `3 * 10 ^ -8`, so about seven decimal places instead of thirteen.
-/

namespace PrimeCert.Sieve

run_sieve 50000000

end PrimeCert.Sieve

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_window 50000000 14 20480 0 3
