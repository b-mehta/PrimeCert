/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # Sieved and summed, file 3 of four (see `Split8_Full`) -/

namespace PrimeCert.Split8_Full2

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1050331649 1048576 100003 20 2048 1536 8 15

end PrimeCert.Split8_Full2
