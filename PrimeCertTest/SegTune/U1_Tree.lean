/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The widest band on the tree, each divisor deriving both its strikes

One arm of a pair. `U2_Derived` is the same window with each divisor's second strike taken from
its first, so the difference between the two is what deriving the second progression costs. -/

namespace PrimeCert.SegTune.U1_Tree

run_sieve 10000000

run_segment_variant 45 100000000000001 4194304 3333332 8192 10000000

end PrimeCert.SegTune.U1_Tree
