/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The primes from `4000702721`, part 18 of 26

56 segments of 1048576 wheel positions, sieved by the primes up to `110017` and summed at
scale `10 ^ 20` by walking the gaps between the survivors. This set of 26 parts carries
`1005969665` to `5586149632`; `Higher.All` joins them.
-/

namespace PrimeCert.Higher.P17

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 4000702721 1048576 110017 20 2048 1536 56 15

end PrimeCert.Higher.P17
