/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Variant timing, divisors up to `10^6`: mode 2 (base-sieve slices)

The `V6_M0a` case through `segLoopSK`, with one slice lemma and one batch lemma per batch. -/

namespace PrimeCert.SegTune.V6_M2

run_segment_variant 2 10000000000000001 4194304 333333 512

end PrimeCert.SegTune.V6_M2
