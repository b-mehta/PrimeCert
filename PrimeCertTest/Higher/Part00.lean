/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The primes from `1005969665` to `1156964608`

192 windows of 262144 wheel positions, sieved by the primes up to `53087` and summed at scale
`10 ^ 20`. One of twelve such files carrying the range from just past `10 ^ 9` to `2817908992`;
`Higher.All` joins them, and `Higher.Total` adds the enclosure below `1005969665` to the result.
-/

namespace PrimeCert.Higher.P00

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1005969665 262144 53087 20 2048 1536 192 1

end PrimeCert.Higher.P00
