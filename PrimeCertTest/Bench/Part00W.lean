/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # `Billion.Part00`'s range in windows of 1048576

The same primes as `Billion.Part00`, twenty-four windows rather than ninety-six, since each window
scans every base prime whatever its width. -/

namespace PrimeCert.Bench.Part00W

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 100000001 1048576 31721 20 2048 1536 24

end PrimeCert.Bench.Part00W
