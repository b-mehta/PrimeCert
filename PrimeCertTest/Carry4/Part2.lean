/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The third of four adjacent ranges, each proved in its own job

One segment of 1048576 wheel positions from 1006291457, covering 1006291457 to 1009437185, where
`Part1` left off.
-/

namespace PrimeCert.Carry4.Part2

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1006291457 1048576 100003 20 2048 1536 1 15

end PrimeCert.Carry4.Part2
