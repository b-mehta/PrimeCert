/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt12

/-! # The `10 ^ 12` window through the clamped loop

`segLoopCK`: a prime whose two starting positions fall outside the window is dropped, the doubling
stops at the window's width, and a step whose mask meets nothing leaves the segment alone. Here
the window holds 262144 positions and the divisors reach 1000001, so most primes have a stride
wider than the window. `SegV0Ht12` is the arm the sum currently uses.
-/

namespace PrimeCert.SegV1Ht12

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_segment_variant 1 1000000000001 262144 333333 1536 2000000

end PrimeCert.SegV1Ht12
