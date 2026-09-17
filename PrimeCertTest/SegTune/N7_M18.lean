/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Mask width, as it is today: the per-batch checks over the primes below two million

The arm `N7_M17` is compared against: the same 456 batches and the same per-batch checks, with the
mask built by doubling as it is today. -/

namespace PrimeCert.SegTune.N7_M18

run_sieve 10000000

run_segment_variant 18 100000000000001 4194304 700416 1536 10000000

end PrimeCert.SegTune.N7_M18
