/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The eight-strike band with each shared subterm of a record written once

`E9_Sorted` reaches every record's seed through `entrySeedK`, which names the divisor's value three
times on the path it takes, and `stripeEntryK` computes that seed twice, once to pick the slice and
once for the bit it sets. This file reaches the same assembled number through `stripeBatchTK`,
where each of those appears once. Same divisors, same records, same value, so the pair against
`E9_Sorted` is the repeated subterms on their own. -/

namespace PrimeCert.SegTune.E7_Shared

run_sieve 10000000

run_segment_variant 37 100000000000001 4194304 3333332 3072 10000000

end PrimeCert.SegTune.E7_Shared
