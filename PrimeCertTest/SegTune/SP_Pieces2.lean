/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The skipped product in two pieces

`SP_Pieces1` with `(parts / 262144) % 4` at 1, so `parts 314819`: the skipped side's product tree
stops with two entries left and a gcd is stated against each.

Pair with `SP_Pieces1`, `SP_Pieces4` and `SP_Pieces8`, one job.

Throwaway. -/

namespace PrimeCert.SegTune.SP_Pieces2

run_sieve 100000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 314819 10000000000000001 4194304 33333333 65536 0 65536 100000000

end PrimeCert.SegTune.SP_Pieces2
