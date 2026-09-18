/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt12

/-! # `Ht12_M3` with the compiled twin that mirrors the clamped loop

The kernel statements are those of `Ht12_M3`; what differs is the elaborator's own computation of
the batch literals, which here mirrors the savings the clamped loop makes rather than walking the
whole base sieve for every index.
-/

namespace PrimeCert.Ht12_M11

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000000001 262144 1000001 20 2048 1536 1 1 11

end PrimeCert.Ht12_M11
