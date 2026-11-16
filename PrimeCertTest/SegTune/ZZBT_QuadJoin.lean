/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCert.SkipSound

/-! # The join with four-record leaves

`ZZBM_JoinProved` with chunk products stated as `prodQuadK` (parts bit 1048576). Pair with `ZZBM`.

Throwaway. -/

namespace PrimeCert.SegTune.ZZBT_QuadJoin

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 1232323 100000000000001 4194304 3333333 8192 0 65536 10000000

#print axioms segEqAll_100000000000001_4194304_3333333

end PrimeCert.SegTune.ZZBT_QuadJoin
