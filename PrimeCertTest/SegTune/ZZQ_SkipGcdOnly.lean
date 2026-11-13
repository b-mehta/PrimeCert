/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The gcd equations alone, over a 65536-bit slice

The other half of `ZZI_SkipFull`: 64 gcd equations and no marking route. Together with
`ZZP_SkipRouteOnly` this says which half of the 40.0-40.3 GB belonged to which, which `ZZI` could
not, having emitted both.

The emitter still does its full marking pass and self-check here, because the skip set is what the
gcds are stated over, so the emitter lines are not a saving to read off this case.

Run it after `ZZP_SkipRouteOnly`, and only if that one shows a saving worth chasing. If marking the
striking divisors alone buys little, which half held the memory stops being an interesting
question.

Throwaway. -/

namespace PrimeCert.SegTune.ZZQ_SkipGcdOnly

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 1 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZQ_SkipGcdOnly
