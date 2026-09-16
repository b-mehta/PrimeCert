/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Variant timing, divisors up to `10^6`: mode 1 (clamped marking)

The `V6_M0a` case through `segLoopCK`. -/

namespace PrimeCert.SegTune.V6_M1

run_segment_variant 1 10000000000000001 4194304 333333 512

end PrimeCert.SegTune.V6_M1
