/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt12

/-! # One window at `10 ^ 12` from two folds

The count of the primes and their total, with the total of their squares replaced by the last
number in the window times that total. `Ht12` and `TaylorHt12` are the arms to compare it with.
-/

namespace PrimeCert.Taylor2Ht12

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000000001 262144 1000001 20 2048 1536 1 9

end PrimeCert.Taylor2Ht12
