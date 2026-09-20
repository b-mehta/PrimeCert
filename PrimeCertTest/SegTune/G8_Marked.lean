/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The divisors that strike the segment many times, marked one at a time

The comparison arm for `G9_Joined`: the same divisors, the same batches, each marking the whole
segment once. -/

namespace PrimeCert.SegTune.G8_Marked

run_sieve 10000000

run_segment_variant 33 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.G8_Marked
