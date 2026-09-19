/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The sorted slices, with the clear a real run owes

The batches over the positions whose primes are past half the window's width, each prime's hits
sorted into slices of the window, and then the window cleared once against the batch's assembled
mask. `Q7_Sorted` times the same batches without that clear; `Q8_Plain` times them the way the
sieve marks them today, the clear being inside its fold. So this file is the arm to compare with
`Q8_Plain`. -/

namespace PrimeCert.SegTune.Q9_Cleared

run_sieve 10000000

run_segment_variant 27 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.Q9_Cleared
