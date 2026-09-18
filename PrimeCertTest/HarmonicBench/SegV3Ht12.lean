/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt12

/-! # The `10 ^ 12` window through the clamped loop reading slices

`segLoopSCK`: the clamping of `SegV1Ht12`, and each batch reads its own slice of the base sieve
rather than the whole of it. `SegV0Ht12` is the arm the sum currently uses.
-/

namespace PrimeCert.SegV3Ht12

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_segment_variant 3 1000000000001 262144 333333 1536 2000000

end PrimeCert.SegV3Ht12
