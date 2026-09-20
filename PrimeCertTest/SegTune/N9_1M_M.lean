/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # A billion, 1048576 positions, marked

The comparison arm for `N9_1M_S`. -/

namespace PrimeCert.SegTune.N9_1M_M

run_segment_variant 20 1000000001 1048576 10545 1536

end PrimeCert.SegTune.N9_1M_M
