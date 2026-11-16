/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The 10^16 window with four-record leaves

`ZZBB_Target1e16Skip` with chunk products stated as `prodQuadK` (parts bit 1048576). Pair with
`ZZBB`, one job, alternating; the groups to read are `cert skip records` and `cert live records`.

Throwaway. -/

namespace PrimeCert.SegTune.ZZBU_Target1e16Quad

run_sieve 100000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 1101251 10000000000000001 4194304 33333333 65536 0 65536 100000000

end PrimeCert.SegTune.ZZBU_Target1e16Quad
