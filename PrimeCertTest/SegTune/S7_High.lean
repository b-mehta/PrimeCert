/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt12

/-! # `S7_Mine` with seven times the divisors, the width held (see `S7_Low`)

Divisors to `1000003`, which is 78498 of them against the 10452 of `S7_Mine`, at the same 1048576
positions from the same start. Most of these exceed the segment, so they strike once or not at
all, which is the case the two-point table could not see.
-/

namespace PrimeCert.SegTune.S7_High

run_segment_variant 20 1005969665 1048576 333334 1536 2000000

end PrimeCert.SegTune.S7_High
