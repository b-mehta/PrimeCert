/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The first of four consecutive segments run at once, the current way

`S9_Par1`'s segment done as `S7_Sched` does it, marking the segment once per divisor throughout.
The group `S7_Par1` to `S7_Par4` is the comparison for the group `S9_Par1` to `S9_Par4`, and both
groups have to run in one job for their numbers to be comparable. -/

namespace PrimeCert.SegTune.S7_Par1

run_sieve 10000000

run_segment_variant 20 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.S7_Par1
