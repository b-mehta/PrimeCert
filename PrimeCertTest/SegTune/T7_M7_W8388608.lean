/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Variant timing, divisors up to `10^7`: both changes and a tree, window 8388608 bits

This window passed 14 GB under every earlier shape. -/

namespace PrimeCert.SegTune.T7_M7_W8388608

run_sieve 10000000

run_segment_variant 7 100000000000001 8388608 3333332 1536 10000000

end PrimeCert.SegTune.T7_M7_W8388608
