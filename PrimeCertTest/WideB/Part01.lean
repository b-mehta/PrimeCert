/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The primes from `1156964609`, part 2 of 4

24 segments of 2097152 wheel positions, sieved by the primes up to `150001` and summed at
scale `10 ^ 20` by walking the gaps between the survivors. This set of 4 parts carries
`1005969665` to `1609949440`; `WideB.All` joins them. The first four parts hold a quarter, a half, three
quarters and a whole file of segments so that four building at once finish at different times and
their peaks stop coinciding.
-/

namespace PrimeCert.WideB.P01

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1156964609 2097152 150001 20 2048 1536 24 15

end PrimeCert.WideB.P01
