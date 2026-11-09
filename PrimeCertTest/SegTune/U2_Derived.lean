/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The widest band on the tree, each divisor's second strike taken from its first

The other arm of the pair described in `U1_Tree`. -/

namespace PrimeCert.SegTune.U2_Derived

run_sieve 10000000

run_segment_variant 58 100000000000001 4194304 3333332 8192 10000000

end PrimeCert.SegTune.U2_Derived
