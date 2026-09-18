/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt14

/-! # One window at `10 ^ 14` (see `Ht09`) -/

namespace PrimeCert.Ht14

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 100000000000001 262144 10000001 20 2048 1536 1 1

end PrimeCert.Ht14
