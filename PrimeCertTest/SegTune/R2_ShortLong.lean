/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The long middle tiers at the divisor count a window near 2.5e13 needs

The other arm of the pair described in `R1_ShortShort`, with the two middle bands in batches of
4096. -/

namespace PrimeCert.SegTune.R2_ShortLong

run_sieve 10000000

run_segment_variant 57 100000000000001 4194304 1666666 8192 10000000

end PrimeCert.SegTune.R2_ShortLong
