/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The joined accumulator over narrow masks, at a quarter of the window

The third arm of the cheap triple described in `ZQ_DoublingQ`. -/

namespace PrimeCert.SegTune.ZS_JoinedQ

run_segment_variant 70 100000000000001 1048576 83333 8192

end PrimeCert.SegTune.ZS_JoinedQ
