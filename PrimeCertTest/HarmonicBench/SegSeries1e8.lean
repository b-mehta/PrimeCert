/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # Eight neighbouring windows above `10 ^ 8` in one line

Eight windows of 262144 wheel positions from `100000001`, about 6.3 million numbers in all, sieved
by the primes up to `31627`, summed and joined. `Seg1e8_W262144` is the first of these eight alone,
so the two together say what each extra window in a file costs.
-/

namespace PrimeCert.SegSeries

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 100000001 262144 31627 20 2048 1536 8

end PrimeCert.SegSeries
