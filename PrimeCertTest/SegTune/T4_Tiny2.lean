/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The second window of the pair described in `T4_Tiny1`

The window after it, matching `S9_Par2`, so the two run together as a runner would take them. -/

namespace PrimeCert.SegTune.T4_Tiny2

run_sieve 10000000

run_segment_variant 28 100000012582913 4194304 37410 8192 10000000

end PrimeCert.SegTune.T4_Tiny2
