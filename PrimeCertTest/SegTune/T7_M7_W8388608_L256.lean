/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Variant timing, divisors up to `10^7`: both changes and a tree, window 8388608, batches of 256

The window that passed 14 GB at batches of 1536, run with 13021 short batches instead. -/

namespace PrimeCert.SegTune.T7_M7_W8388608_L256

run_sieve 10000000

run_segment_variant 7 100000000000001 8388608 3333332 256 10000000

end PrimeCert.SegTune.T7_M7_W8388608_L256
