/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # One window at `10 ^ 13` (see `Ht09`) -/

namespace PrimeCert.Ht13

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 10000000000001 262144 3162281 20 2048 1536 1 1

end PrimeCert.Ht13
