/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # A gap-walked segment of 4194304 positions at the record's divisor bound (see `GapW0262`)

The first round of that sweep had the cost per position still falling at the widest case it held,
10.76, 8.73 and 7.67 microseconds of kernel at 524288, 1048576 and 2097152 positions, so the sweep
needs a case beyond it to find where it turns.
-/

namespace PrimeCert.GapW4194

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 4194304 110017 20 2048 1536 1 15

end PrimeCert.GapW4194
