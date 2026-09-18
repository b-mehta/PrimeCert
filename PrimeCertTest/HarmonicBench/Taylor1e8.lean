/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # One window above `10 ^ 8` through the offset expansion

The same window as `Bitn1e8_F1`, with the reciprocal fold replaced by the three folds of equation
(8.2) of Bach, Klyve and Sorenson: the count of the primes, the total of the primes themselves and
the total of their squares. No division happens per prime; the two that rescale the enclosure to
the denominator `10 ^ 20` are done once for the window while the statement is built. `Bitn1e8_F1`
is the arm to compare it with.
-/

namespace PrimeCert.Taylor1e8

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 100000001 262144 31721 20 2048 1536 1 8

end PrimeCert.Taylor1e8
