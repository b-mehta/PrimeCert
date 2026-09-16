/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Segment timing: divisors up to `10^6`, segment 262144 bits

One segment of 262144 bits starting at `10^16 + 1`, sieved by the divisors at wheel positions
`1 … 333333` of the cached `10^6` sieve, in batches of 512 steps (652 batch lemmas). -/

namespace PrimeCert.SegTune.T6_W262144

run_segment 10000000000000001 262144 333333 512

end PrimeCert.SegTune.T6_W262144
