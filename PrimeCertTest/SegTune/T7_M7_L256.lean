/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Variant timing, divisors up to `10^7`: both changes and a tree, batches of 256 steps

13021 batches, combined in a tree. -/

namespace PrimeCert.SegTune.T7_M7_L256

run_sieve 10000000

run_segment_variant 7 100000000000001 4194304 3333332 256 10000000

end PrimeCert.SegTune.T7_M7_L256
