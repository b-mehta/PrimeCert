/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The same walk enclosed over a narrower segment

`Form16` encloses 65536 positions in one interval; this encloses 2048. The offsets from the
segment's own first number are thirty-two times smaller, so the width the expansion leaves should
fall with the cube of that while the number of segments rises linearly, which is the trade the
enclosure granularity controls.
-/

namespace PrimeCert.GapAB.Form16Narrow

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 2048 100003 20 2048 1536 1 16

end PrimeCert.GapAB.Form16Narrow
