/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The primes from `100000001` to `175497472`

96 windows of 262144 wheel positions, sieved by the primes up to `31627` and summed at scale
`10 ^ 20`. One of twelve such files covering `10 ^ 8` to just past `10 ^ 9`; `Billion.All` joins
them.
-/

namespace PrimeCert.Billion.P00

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 100000001 262144 31627 20 2048 1536 96

end PrimeCert.Billion.P00
