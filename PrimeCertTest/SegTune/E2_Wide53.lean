/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The whole segment with the widest band through a 262144-bit-leaf tree

`E2_Rec2` settles every band by sorted records. This settles the divisors whose double already
passes the end of the segment by `wtreeStep2`, leaving the other two bands as they are, so the
pair measures the change over a real certificate rather than over a band probe. -/

namespace PrimeCert.SegTune.E2_Wide53

run_sieve 10000000

run_segment_variant 53 100000000000001 4194304 3333332 3072 10000000

end PrimeCert.SegTune.E2_Wide53
