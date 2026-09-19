/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The many-strike divisors, every batch given the segment's round count

The comparison arm for `R9_Rounds`: the same divisors and batches, each handed the 22 doublings the
whole segment needs. -/

namespace PrimeCert.SegTune.R8_Global

run_sieve 10000000

run_segment_variant 33 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.R8_Global
