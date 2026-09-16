/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # One small window above a sieve, sieved and summed

Dividing only by the primes up to `101`, so the window must start at or above `707` and stay below
`101 ^ 2 = 10201`. It covers 300 wheel positions from `707`, the numbers `707` to `1603`, and the
enclosure is over the primes among them at scale `10 ^ 12`.
-/

namespace PrimeCert.SegSmall

run_segment 707 300 33 8

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_segment 707 300 101 12 64 8

end PrimeCert.SegSmall
