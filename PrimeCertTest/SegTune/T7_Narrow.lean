/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Batch length varying with the size of the primes

`V7_M11` with short batches over the small primes and long ones over the large primes, in place of
1536 throughout. Same segment, same divisors, same emitted statements. -/

namespace PrimeCert.SegTune.T7_Narrow

run_sieve 10000000

run_segment_variant 20 100000000000001 4096 3333332 1536 10000000

end PrimeCert.SegTune.T7_Narrow
