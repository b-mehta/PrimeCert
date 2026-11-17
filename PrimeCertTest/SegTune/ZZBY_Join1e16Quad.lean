/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCert.SkipSound

/-! # The proved window at the depth it is for, both chunk trees wide

`ZZBX_Join1e16Narrow` with both wide-leaf bits on, so `parts 3329475`: chunk products as
`prodQuadK`, chunk assemblies as `asmQuadK`, four records a leaf each, and the per-window theorem
emitted with its proof.

This is the shape a run would ship, and the one measurement that would justify making the wide
leaves the default rather than a flag. Read `cert skip records`, `cover asm`, the kernel total and
the peak, and the `AXIOMS` line that `run.sh` lifts out of the case's own log.

Pair with `ZZBX_Join1e16Narrow`, one job.

Throwaway. -/

namespace PrimeCert.SegTune.ZZBY_Join1e16Quad

run_sieve 100000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 3329475 10000000000000001 4194304 33333333 65536 0 65536 100000000

#print axioms segEqAll_10000000000000001_4194304_33333333

end PrimeCert.SegTune.ZZBY_Join1e16Quad
