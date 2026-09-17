/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # Four windows above `10 ^ 8`, with the bit test as it stands

The short version of `Bit1e8_F1`, for iterating on the five forms quickly; the winner is confirmed
at 24 windows before it goes into a run.
-/

namespace PrimeCert.Bits1e8.F1

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 100000001 262144 31721 20 2048 1536 4 1

end PrimeCert.Bits1e8.F1
