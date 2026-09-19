/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # One window above `10 ^ 8`, crossed off by the loop in use until now

The window of `Bitn1e8_F1`, pinned to the loop that walks every base index and builds a full mask
for each prime. Here the divisors reach only 31721 and the window covers 262144 positions, so no
prime has a stride wider than the window, which is the case the clamping was for. `Bitn1e8_M11` is
the arm to compare it with.
-/

namespace PrimeCert.Bitn1e8_M0

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 100000001 262144 31721 20 2048 1536 1 1 0

end PrimeCert.Bitn1e8_M0
