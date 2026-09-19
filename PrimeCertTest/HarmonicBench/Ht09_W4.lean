/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # Twice the width of `Ht09_F7W2`, at the height the record run works at

1048576 positions rather than 524288, the same start, the same divisors to 100003 and the same
sum with the count bounded by the width. At `10 ^ 12` the wider segment cost 10.89 microseconds
per integer against 11.48; this asks whether that holds at `10 ^ 9`, where the divisors are far
smaller relative to the width.
-/

namespace PrimeCert.Ht09_W4

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 1048576 100003 20 2048 1536 1 7

end PrimeCert.Ht09_W4
