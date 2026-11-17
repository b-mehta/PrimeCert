/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCertTest.SegTune.Base1e7

/-! # What an imported `10^7` base costs before anything uses it

The smallest of the floor cases. `S14_BaseFloor1e8` is the same for `10^8`, and `Base0_Startup`
carries the imports both of them carry and no sieve at all, so the three read together give the
charge for the sieve alone at two sizes a factor of ten apart.

Throwaway. -/

namespace PrimeCert.SegTune.S15_BaseFloor1e7

end PrimeCert.SegTune.S15_BaseFloor1e7
