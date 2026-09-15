/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Variant timing, divisors up to `10^7`: both changes and a tree, window 262144 bits

A sixteenth of `T7_M7`'s window, for checking time per candidate against window size. -/

namespace PrimeCert.SegTune.T7_M7_W262144

run_sieve 10000000

run_segment_variant 7 100000000000001 262144 3333332 1536 10000000

end PrimeCert.SegTune.T7_M7_W262144
