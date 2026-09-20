/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The primes from `1458954497`, part 4 of 4

12 segments of 4194304 wheel positions, sieved by the primes up to `150001` and summed at
scale `10 ^ 20` by walking the gaps between the survivors. This set of 4 parts carries
`1005969665` to `1609949440`; `WideA.All` joins them. The first four parts hold a quarter, a half, three
quarters and a whole file of segments so that four building at once finish at different times and
their peaks stop coinciding.
-/

namespace PrimeCert.WideA.P03

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1458954497 4194304 150001 20 2048 1536 12 15

end PrimeCert.WideA.P03
