/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The smallest band's masks built by doubling

One arm of a pair. `W2_Multiply` is the same window with each doubling round done as a
multiplication, so the difference between the two is what building those masks costs. -/

namespace PrimeCert.SegTune.W1_Double

run_sieve 10000000

run_segment_variant 62 100000000000001 4194304 3333332 8192 10000000

end PrimeCert.SegTune.W1_Double
