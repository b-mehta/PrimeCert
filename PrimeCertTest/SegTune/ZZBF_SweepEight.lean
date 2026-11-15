/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The sweep taken down to the small band

`parts 19907`: `ZZBE_SweepFour` with the sweep starting at the eight-strike band, so that only the
masked small band is marked plainly and everything above it is tested.

Here only if `ZZBE_SweepFour` wins, and in the repository rather than generated on a box, because
the `10^15` arms were generated on one and the point nearly went with it when the box terminated.

The band is the least rewarding of the three: 37.0% skippable at `10^14` and 41.5% at `10^15`,
against the four-strike band's 60.2% and 64.2%. It is also the last one available — below it is
the base the sweep tests against, which cannot test itself.

Soundness is the same argument at every setting. A divisor that strikes nothing live in the base
strikes nothing in the finished window, because marking only clears bits; and testing against a
base with more live bits than the final window can only make a divisor look like a striker when it
is not, never the reverse. So leaving the base as the small band while sweeping everything above
it needs nothing new.

Pair with whichever of `ZZAH_OneGcd1024` and `ZZBE_SweepFour` won, one job, alternating.

Throwaway. -/

namespace PrimeCert.SegTune.ZZBF_SweepEight

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 19907 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZBF_SweepEight
