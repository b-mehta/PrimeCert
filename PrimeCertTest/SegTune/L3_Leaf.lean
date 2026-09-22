/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # A batch assembled through leaves of 262144 bits and of 1048576

The window of 4194304 bits holds 16 leaves at the first width and 4 at the second.

Mode 50 settles each batch of the widest band both ways, alternating which goes first. `run.sh`
reports the 262144-bit width under `batch lemmas` and the 1048576-bit width under `sorted batch
lemmas`. -/

namespace PrimeCert.SegTune.L3_Leaf

run_sieve 10000000

run_segment_variant 50 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.L3_Leaf
