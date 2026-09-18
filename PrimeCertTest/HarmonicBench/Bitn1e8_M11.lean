/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # One window above `10 ^ 8`, crossed off by the clamped loop reading slices

The window of `Bitn1e8_M0`, with the loop that drops a prime whose starting positions miss the
window, stops the doubling at the window's width, skips the masks meeting nothing, and reads each
batch's own slice of the base sieve. This is the height the record run works at.
-/

namespace PrimeCert.Bitn1e8_M11

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 100000001 262144 31721 20 2048 1536 1 1 11

end PrimeCert.Bitn1e8_M11
