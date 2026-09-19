/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The `10 ^ 9` stretch crossed off and its primes counted

Between `SegOnlyHt09`, which stops after crossing off, and `Ht09`, which also adds a quotient for
each surviving prime.
-/

namespace PrimeCert.CountHt09

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 262144 31637 20 2048 1536 1 11

end PrimeCert.CountHt09
