/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCert.SkipSound

/-! # The proved window at the depth it is for, both chunk trees narrow

`parts 183747`: the settled shape at `10^16` with the per-window theorem emitted and proved, which
is `ZZBB_Target1e16Skip` plus `(parts / 131072) % 2`.

The baseline for `ZZBY_Join1e16Quad`. Until now the two wide-leaf bits had been priced at `10^16`
without the join and at `10^14` with it, and the shape a run would actually ship, a proved window
at the target depth, had been measured with neither.

Pair with `ZZBY_Join1e16Quad`, one job.

Throwaway. -/

namespace PrimeCert.SegTune.ZZBX_Join1e16Narrow

run_sieve 100000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 183747 10000000000000001 4194304 33333333 65536 0 65536 100000000

#print axioms segEqAll_10000000000000001_4194304_33333333

end PrimeCert.SegTune.ZZBX_Join1e16Narrow
