/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt12

/-! # Crossing off the `10 ^ 12` window through the loop the sum uses

`runSegment`, which `run_harmonic_series` calls, walks every base index and builds a full mask for
each prime. `SegV1Ht12` and `SegV3Ht12` are the same window through the two loops that were tuned
for divisors to `10 ^ 7` and a segment sixteen times as wide, which is a different regime from
this one.
-/

namespace PrimeCert.SegV0Ht12

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_segment_variant 0 1000000000001 262144 333333 1536 2000000

end PrimeCert.SegV0Ht12
