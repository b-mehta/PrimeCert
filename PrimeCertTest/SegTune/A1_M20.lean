/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same segment with the graded batch length

`A1_M11` with batches whose length varies with the size of the divisors, short at the small end and
long at the large end, in place of 1536 throughout. -/

namespace PrimeCert.SegTune.A1_M20

run_segment_variant 20 1000000001 524288 33334 1536

end PrimeCert.SegTune.A1_M20
