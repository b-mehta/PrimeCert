/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The second of four adjacent ranges, each proved in its own job

One segment of 1048576 wheel positions from 1003145729, covering 1003145729 to 1006291457, where
`Part0` left off.
-/

namespace PrimeCert.Carry4.Part1

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1003145729 1048576 100003 20 2048 1536 1 15

end PrimeCert.Carry4.Part1
