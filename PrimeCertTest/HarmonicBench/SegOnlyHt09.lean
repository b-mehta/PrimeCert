/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The crossing off of the `10 ^ 9` stretch on its own

`Ht09` crosses off the same stretch and then sums over what survives, and `CountHt09` stops after
counting the survivors. The three together say how a stretch's cost divides at the height the
record run works at, where the divisors reach only 31637.
-/

namespace PrimeCert.SegOnlyHt09

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_segment 1000000001 262144 10545 1536

end PrimeCert.SegOnlyHt09
