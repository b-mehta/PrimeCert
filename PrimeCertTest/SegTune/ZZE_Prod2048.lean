/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The production path at a quarter of the batch length

The third point of the pair described in `ZZD_Prod4096`, so that a win at 4096 can be told from a
trend. Shorter batches mean more of them, and each carries its own chain step and literal, so
there is a length below which it turns around; this is to find which side of it 4096 sits on. -/

namespace PrimeCert.SegTune.ZZE_Prod2048

run_sieve 10000000

run_segment_variant 28 100000000000001 4194304 333333 2048 10000000

end PrimeCert.SegTune.ZZE_Prod2048
