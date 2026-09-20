/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The primes from `2213929217`, part 5 of 33

96 segments of 1048576 wheel positions, sieved by the primes up to `110017` and summed at
scale `10 ^ 20`, with the count of primes in a segment bounded by its width so that only the
quotients are summed. `Higher.All` joins the 33 parts, which together carry the range from
just past `10 ^ 9` to `10971635969`, and the enclosure below `1005969665` is added to that.
-/

namespace PrimeCert.Higher.P04

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 2213929217 1048576 110017 20 2048 1536 96 15

end PrimeCert.Higher.P04
