/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # One window above `10 ^ 8` with no count of the primes

The same window as `Bitn1e8_F1`, with the walk that counts the primes dropped and the number of
positions in the window used as the bound on that count instead. `Bitn1e8_F1` is the arm to compare
it with.
-/

namespace PrimeCert.Nocount1e8

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 100000001 262144 31721 20 2048 1536 1 7

end PrimeCert.Nocount1e8
