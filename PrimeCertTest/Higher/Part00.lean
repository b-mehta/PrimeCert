/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The primes from `1005969665`, part one of twelve

240 segments of 524288 wheel positions, sieved by the primes up to `100003` and summed at scale
`10 ^ 20`, with the count of primes in a segment bounded by its width so that only the quotients
are summed. One of twelve such files carrying the range from just past `10 ^ 9` to `5535817985`;
`Higher.All` joins them, and the enclosure below `1005969665` is added to that.
-/

namespace PrimeCert.Higher.P00

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1005969665 524288 100003 20 2048 1536 240 7

end PrimeCert.Higher.P00
