/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # One full sized window just above `10 ^ 8`, sieved and summed

4194304 wheel positions from `100000001`, that is about 12.6 million consecutive numbers, sieved by
the primes up to `31627` and summed at scale `10 ^ 20`. Dividing by primes to `31627` suffices as
long as the numbers stay below `31627 ^ 2`, which is just over `10 ^ 9`.
-/

namespace PrimeCert.Seg1e8

run_segment 100000001 4194304 10542 1536

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_segment 100000001 4194304 31627 20 2048 1536

end PrimeCert.Seg1e8
