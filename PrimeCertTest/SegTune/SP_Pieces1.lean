/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The skipped product whole: the baseline arm

`ZZBB_Target1e16Skip` unchanged, `parts 52675`, so the skipped side ends at one literal holding
all 5519007 skipped divisors and one gcd is stated against it.

The baseline for `SP_Pieces2`, `SP_Pieces4` and `SP_Pieces8`, which stop the same product tree
with 2, 4 and 8 entries left. All four in one job, so the four share a runner.

Throwaway. -/

namespace PrimeCert.SegTune.SP_Pieces1

run_sieve 100000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 52675 10000000000000001 4194304 33333333 65536 0 65536 100000000

end PrimeCert.SegTune.SP_Pieces1
