/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The first of four consecutive segments run at once

`S9_Stripes` on the segment starting at 100000000000001. The four files `S9_Par1` to `S9_Par4`
cover four consecutive stretches and are run together, so that the group says how many segments a
runner gets through per hour, which is what the whole computation is priced in. -/

namespace PrimeCert.SegTune.S9_Par1

run_sieve 10000000

run_segment_variant 28 100000000000001 4194304 3333332 16384 10000000

end PrimeCert.SegTune.S9_Par1
