/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The second of four files built together (see `Par0`) -/

namespace PrimeCert.Par1

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1150994945 1048576 100003 20 2048 1536 48 15

end PrimeCert.Par1
