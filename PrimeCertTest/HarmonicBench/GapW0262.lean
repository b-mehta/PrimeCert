/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # A gap-walked segment of 262144 positions at the record's divisor bound

The segment width was last chosen for the walk over every position, at a height of `10 ^ 12` and
with the strikes sorted. The record attempt runs at a tenth of that height with the gap walk and
with nothing sorting, so these four files sweep the width again at the attempt's own parameters:
start just past `10 ^ 9`, divisors to `110017`, batches of 1536 positions. The `gapwidth` job times
each with the kernel check on and off, since the gap walk moved a third of the cost to the
elaborator.
-/

namespace PrimeCert.GapW0262

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 262144 110017 20 2048 1536 1 15

end PrimeCert.GapW0262
