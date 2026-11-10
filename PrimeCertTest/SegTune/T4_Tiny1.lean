/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The first window of a pair sieved as a low window of the range would be

Window 1000 of 1..10^14 needs divisors to 112229, which is fuel 37410, about a hundredth of what
the topmost window needs. Most windows of the range are this cheap, so the mean over the range
leans on the cost model here far more than at the top, and that end of the model has only been
counted. Timing this pair against `S9_Par1` and `S9_Par2` tests it. -/

namespace PrimeCert.SegTune.T4_Tiny1

run_sieve 10000000

run_segment_variant 28 100000000000001 4194304 37410 8192 10000000

end PrimeCert.SegTune.T4_Tiny1
