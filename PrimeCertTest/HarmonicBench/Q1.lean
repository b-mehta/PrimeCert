/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The second of the four files of `Q0` -/

namespace PrimeCert.Q1

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1075497473 1048576 100003 20 2048 1536 24 15

end PrimeCert.Q1
