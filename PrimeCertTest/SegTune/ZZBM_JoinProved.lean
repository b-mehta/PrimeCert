/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCert.SkipSound

/-! # The join, proved

`parts 183747`: `ZZBK_ShallowBase` with the per-window theorem emitted and proved. It states that
marking by every divisor gives the window the route built from the marked subset, and proves it
through `segLoopK_eq_of_join` from the split identity, the route's theorem and the record
certificate.

Pair with `ZZBK_ShallowBase`, one job, alternating, peak each. The line to read is `join proved:`,
which times the split identity, the two slice covers and the window theorem apart.

Throwaway. -/

namespace PrimeCert.SegTune.ZZBM_JoinProved

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 183747 100000000000001 4194304 3333333 8192 0 65536 10000000

#print axioms segEqAll_100000000000001_4194304_3333333

end PrimeCert.SegTune.ZZBM_JoinProved
