/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # 4194304 positions in one window

Against `W1M`, which covers the same positions in four windows of 1048576, to find where widening
stops paying. -/

namespace PrimeCert.Bench.W4M

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 100000001 4194304 31721 20 2048 1536 1

end PrimeCert.Bench.W4M
