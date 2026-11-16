/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCert.SkipSound

/-! # The proved skip shape at batches of 65536

`ZZBM_JoinProved` with the batch length eight times as long. Pair with `ZZBM_JoinProved`, one job,
alternating. -/

namespace PrimeCert.SegTune.SB_M65536

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 183747 100000000000001 4194304 3333333 65536 0 65536 10000000

#print axioms segEqAll_100000000000001_4194304_3333333

end PrimeCert.SegTune.SB_M65536
