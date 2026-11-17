/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The `10^9` base in batches of eight

`S10_Sieve1e18Base` with the batch length at 8 rather than the default 16, the midpoint between
that default and `S11_Base1e18Len4`.

Three points rather than two, because the notes record the stage count as a U-shaped trade against
memory, so a line through 16 and 4 would say nothing about what lies between them.

Pair with `S11_Base1e18Len4` and `S10_Sieve1e18Base`, one job.

Throwaway. -/

namespace PrimeCert.SegTune.S12_Base1e18Len8

run_sieve 1000000000 8

end PrimeCert.SegTune.S12_Base1e18Len8
