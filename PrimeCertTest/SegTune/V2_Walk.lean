/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The widest band's walk priced apart from its strikes

`U1_Tree` emits the widest band on the tree. This emits the same statements and, per batch of that
band, one more that walks the batch's positions and counts the divisors it names without placing a
strike. The difference between the two runs is therefore the walk alone. -/

namespace PrimeCert.SegTune.V2_Walk

run_sieve 10000000

run_segment_variant 59 100000000000001 4194304 3333332 8192 10000000

end PrimeCert.SegTune.V2_Walk
