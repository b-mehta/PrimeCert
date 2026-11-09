/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The widest band's strike arithmetic priced apart from its dispatch

`U1_Tree` emits the widest band on the tree and `V2_Walk` adds the bare walk of its positions.
This adds instead the sum of the strike positions those divisors give, found by the same
arithmetic and added rather than placed, so against `V2_Walk` it isolates the arithmetic and
against the band's own cost it leaves the dispatch into leaves. -/

namespace PrimeCert.SegTune.V3_Seed

run_sieve 10000000

run_segment_variant 60 100000000000001 4194304 3333332 8192 10000000

end PrimeCert.SegTune.V3_Seed
