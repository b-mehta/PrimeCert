/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The fourth of four consecutive segments run at once, the current way

`S9_Par4`'s segment done as `S7_Sched` does it. -/

namespace PrimeCert.SegTune.S7_Par4

run_sieve 10000000

run_segment_variant 20 100000037748737 4194304 3333332 1536 10000000

end PrimeCert.SegTune.S7_Par4
