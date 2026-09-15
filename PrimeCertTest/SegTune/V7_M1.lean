/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Variant timing, divisors up to `10^7`: mode 1 (clamped marking)

The `V7_M0a` case through `segLoopCK`. -/

namespace PrimeCert.SegTune.V7_M1

run_sieve 10000000

run_segment_variant 1 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.V7_M1
