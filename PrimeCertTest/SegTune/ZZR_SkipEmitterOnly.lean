/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The skip set computed and nothing emitted

`parts 6`: the marking pass that works out which divisors strike, and then no gcd equations, no
marking route and no self-check. Nothing is emitted at all, so this declares nothing and proves
nothing.

It exists because `ZZP_SkipRouteOnly` ran away past 40 GB with the gcds already switched off, and
`TUNE=0` did not change that, so the allocator is not the cause either. What is left in the frame
is the emitter, and this strips it to the single pass. If this alone runs away, it is
`segLoopHits`; if it does not, the cost is in what follows it.

Run it **once**, not three times, and read peak rather than seconds. It should also print the
skip-set lines, which `ZZP` never reached, so this is the first chance to see the 167446 / 497131
cross-check on a full window.

Throwaway. -/

namespace PrimeCert.SegTune.ZZR_SkipEmitterOnly

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 6 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZR_SkipEmitterOnly
