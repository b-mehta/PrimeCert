/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # A batch assembled through leaves of 65536 bits and of 262144

A strike is placed into one leaf, and the leaves are joined into the window's mask. The window of
4194304 bits holds 128 leaves at the first width and 16 at the second.

Mode 49 settles each batch of the widest band both ways, alternating which goes first. `run.sh`
reports the 65536-bit width under `batch lemmas` and the 262144-bit width under `sorted batch
lemmas`. -/

namespace PrimeCert.SegTune.L2_Leaf

run_sieve 10000000

run_segment_variant 49 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.L2_Leaf
