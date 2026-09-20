/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Tree dispatch over the band where a divisor strikes three or four times

The third and last band. The tree beat the sorted records by 48 percent over the divisors that
strike at most twice and by 3.8 percent over those that strike up to eight times, in both cases
deriving exactly the number of strikes the band has. This derives four, against `B9_Sorted`, which
sorts four records to a divisor over the same divisors. -/

namespace PrimeCert.SegTune.E3_Tree4

run_sieve 10000000

run_segment_variant 44 100000000000001 4194304 3333332 3072 10000000

end PrimeCert.SegTune.E3_Tree4
