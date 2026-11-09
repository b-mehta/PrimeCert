/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The smallest band's masks built by multiplication

The other arm of the pair described in `W1_Double`. -/

namespace PrimeCert.SegTune.W2_Multiply

run_sieve 10000000

run_segment_variant 63 100000000000001 4194304 3333332 8192 10000000

end PrimeCert.SegTune.W2_Multiply
