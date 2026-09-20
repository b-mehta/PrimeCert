/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # A segment at `10 ^ 9` cut into batches of 1024 positions

`Ht09_W4` is the same segment in batches of 2048, `Bat4096` and `Bat8192` in batches of four and
eight thousand. The batch length decides how many theorems the segment's fold is cut into and how
long each one's chain is, and it has never been swept at this width.
-/

namespace PrimeCert.Bat1024

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 1048576 100003 20 1024 1536 1 7

end PrimeCert.Bat1024
