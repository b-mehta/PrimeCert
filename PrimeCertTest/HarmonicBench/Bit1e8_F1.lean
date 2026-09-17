/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # 24 windows above `10 ^ 8`, with the bit test as it stands

The reference arm of the five. `Bit1e8_F2` states each batch with a step-free fold and a matching
bridge, and `F3`, `F4`, `F5` vary the bit test itself.
-/

namespace PrimeCert.Bit1e8.F1

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 100000001 262144 31721 20 2048 1536 24 1

end PrimeCert.Bit1e8.F1
