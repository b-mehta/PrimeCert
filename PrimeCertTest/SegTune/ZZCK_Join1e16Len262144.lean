/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCert.SkipSound

/-! # The proved window at `10^16` with a route batch of 262144

The long arm of the sweep `ZZCJ_Join1e16Len131072` describes, four times the setting in use.

Throwaway. -/

namespace PrimeCert.SegTune.ZZCK_Join1e16Len262144

run_sieve 100000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 3329475 10000000000000001 4194304 33333333 262144 0 65536 100000000

#print axioms segEqAll_10000000000000001_4194304_33333333

end PrimeCert.SegTune.ZZCK_Join1e16Len262144
