/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt12

/-! # The sieving of the `10 ^ 12` window on its own

Every arm at this window start pays for the same crossing off of composites before it sums
anything. This file stops after that step, so the difference from `Ht12` is what the summing
costs.
-/

namespace PrimeCert.SegOnlyHt12

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_segment 1000000000001 262144 333333 1536

end PrimeCert.SegOnlyHt12
