/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The fourth of four position-walk files built together (see `Par0W`) -/

namespace PrimeCert.Par3W

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1452984833 1048576 100003 20 2048 1536 48 7

end PrimeCert.Par3W
