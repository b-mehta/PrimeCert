/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Variant timing, divisors up to `10^7`: both changes and a tree, batches of 512 steps

Batches this short were out of reach while the batches were combined in one chain, which the
kernel rejected past about 2605 links; the tree has no such limit. 6511 batches. -/

namespace PrimeCert.SegTune.T7_M7_L512

run_sieve 10000000

run_segment_variant 7 100000000000001 4194304 3333332 512 10000000

end PrimeCert.SegTune.T7_M7_L512
