/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Variant timing, divisors up to `10^7`: base-sieve slices, batches joined in a tree

`V7_M2` with the batches combined two at a time instead of in one chain. -/

namespace PrimeCert.SegTune.T7_M6

run_sieve 10000000

run_segment_variant 6 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.T7_M6
