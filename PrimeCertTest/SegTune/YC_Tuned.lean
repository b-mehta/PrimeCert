/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # One window at fuel 1666666, divisors to 4999999, reaching every band, on the tuned elaborator -/

namespace PrimeCert.SegTune.YC_Tuned

run_sieve 10000000

run_segment_variant 28 100000000000001 4194304 1666666 8192 10000000

end PrimeCert.SegTune.YC_Tuned
