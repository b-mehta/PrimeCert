/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # A gap-walked segment of 524288 positions at the record's divisor bound (see `GapW0262`) -/

namespace PrimeCert.GapW0524

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 524288 110017 20 2048 1536 1 15

end PrimeCert.GapW0524
