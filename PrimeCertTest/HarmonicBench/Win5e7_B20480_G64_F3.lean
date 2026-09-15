/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Bound `5 * 10 ^ 7`, windows of 20480 positions, segments of 64, packed fold

As `Win5e7_B20480_F3`, with the 814 batches grouped into segments of 64, so the final chain joins 13
segment totals instead of 814 batch totals.
-/

namespace PrimeCert.Sieve

run_sieve 50000000

end PrimeCert.Sieve

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_window 50000000 20 20480 64 3
