/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The first window of a mode-57 pair

`S9_Par1` and `S9_Par2` are the two windows a runner takes at once, and the 27.4 runner-years came
from timing that pair. This is the same first window under the longer middle tiers, so the gain
measured one file at a time can be read again in the shape the costing used. -/

namespace PrimeCert.SegTune.T1_Par1

run_sieve 10000000

run_segment_variant 57 100000000000001 4194304 3333332 8192 10000000

end PrimeCert.SegTune.T1_Par1
