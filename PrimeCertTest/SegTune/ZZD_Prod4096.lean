/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The production path at half the batch length

`WA_Narrow` is this case at 8192, which a sweep settled on. On the sorted band alone, 4096
measured 8.9 percent less kernel than 8192, as the control arm of a three-way test that was really
about something else. That band is part of a production window, so the question is whether the
same holds for the whole of mode 28, where the small band and the chain are also in play.

Pair with `WA_Narrow`, and with `ZZE_Prod2048` to see whether it keeps going down. -/

namespace PrimeCert.SegTune.ZZD_Prod4096

run_sieve 10000000

run_segment_variant 28 100000000000001 4194304 333333 4096 10000000

end PrimeCert.SegTune.ZZD_Prod4096
