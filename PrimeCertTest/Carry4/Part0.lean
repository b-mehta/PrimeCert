/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The first of four adjacent ranges, each proved in its own job

One segment of 1048576 wheel positions from 1000000001, covering 1000000001 to 1003145729. The
`carry4` workflow builds this file in one job and hands the compiled output to the job that joins
all four, so no job reproves another's range.
-/

namespace PrimeCert.Carry4.Part0

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 1048576 100003 20 2048 1536 1 15

end PrimeCert.Carry4.Part0
