/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCert.SkipSound

/-! # The proved window at `10^17`, with each cover slice its own declaration

`ZZBP_Target1e17Skip` with `(parts / 4194304) % 2` on, so `parts 7524291`: the join's cover chains
are added a slice at a time rather than as one term for all of them.

Read against `ZZBP_Target1e17Skip`, which is the same window with the chain checked in one
declaration. Both carry `sliceCov_step`, so whatever separates them is the staging alone and not
the spelling fix that came with it.

The staging exists because a single `addDecl` over 1609 slices was what crossed the watchdog
before that fix. Whether it is still needed is exactly what this pair says, and either answer is
worth having: an unnecessary flag should be dropped rather than left to be rediscovered.

Pair with `ZZBP_Target1e17Skip`, one job.

Throwaway. -/

namespace PrimeCert.SegTune.ZZCC_Target1e17Staged

run_sieve 316300000

set_option maxRecDepth 1000000 in
run_segment_skip_part 7524291 100000000000000001 4194304 105433333 65536 0 65536 316300000

#print axioms segEqAll_100000000000000001_4194304_105433333

end PrimeCert.SegTune.ZZCC_Target1e17Staged
