/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # A quarter of the divisors, to see how a part's memory compares with the whole

The same segment and the same per-batch checks as `V7_M11`, over the first quarter of the base
sieve's indices. Peak memory here against the whole run's decides whether splitting a segment
across parallel processes can fit a 16 GB runner. -/

namespace PrimeCert.SegTune.Q7_Quarter

run_sieve 10000000

run_segment_variant 18 100000000000001 4194304 833333 1536 10000000

end PrimeCert.SegTune.Q7_Quarter
