/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # A window of 131072 positions just above `10 ^ 8`

About 393 thousand numbers. The sieving of a window costs the same whatever its size, so there is a
size below which that cost dominates; this and its neighbours in the sweep say where.
-/

namespace PrimeCert.Seg1e8W17

run_segment 100000001 131072 10542 1536

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_segment 100000001 131072 31627 20 2048 1536

end PrimeCert.Seg1e8W17
