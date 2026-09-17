/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # 4194304 positions in four windows of 1048576

The arm to compare `W4M` against: same positions, four scans of the base primes rather than one,
and operands a quarter the width. -/

namespace PrimeCert.Bench.W1M

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 100000001 1048576 31721 20 2048 1536 4

end PrimeCert.Bench.W1M
