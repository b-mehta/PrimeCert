/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Variant timing, divisors up to `10^6`: mode 0 (the current loop), first copy

One window of 4194304 bits from `10^16 + 1`, sieved by the divisors at wheel positions
`1 … 333333` of the cached `10^6` sieve, in batches of 512 steps (652 batch lemmas). -/

namespace PrimeCert.SegTune.V6_M0a

run_segment_variant 0 10000000000000001 4194304 333333 512

end PrimeCert.SegTune.V6_M0a
