/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Marking only the striking divisors, certifying nothing

The full window with the marking route over the marked subset and **no gcd equations at all**.
Certifying nothing makes this unsound as a sieve, and that is the point: no certificate can cost
less than nothing, so **this is the upper bound on what the whole idea can buy**. Against
`ZZH_FullWindow28` it says what marking 167446 divisors instead of 664577 is worth, before any
question of how to certify the other 497131.

Read it that way round. If this saves little against the control, the gcd certificate's 40 GB
stops mattering, because there would be nothing left for a cheaper certificate to win, and the
skip idea is finished whatever shape the certificate takes. If it saves a lot, then the 40 GB is
the thing to attack and a certificate other than one gcd per slice is worth looking for.

It also splits the 40 GB. `ZZI_SkipFull` emitted the route and the gcds together; this is the
route alone and `ZZQ_SkipGcdOnly` the gcds alone, so the two say which half the memory was in.

Pair with `ZZH_FullWindow28`, both arms in one job, peak for each.

Throwaway. -/

namespace PrimeCert.SegTune.ZZP_SkipRouteOnly

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 2 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZP_SkipRouteOnly
