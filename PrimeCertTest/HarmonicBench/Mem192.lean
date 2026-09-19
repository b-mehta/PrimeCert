/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # A hundred and ninety-two segments in one file, to find where its peak stops growing

`Mem12` and `Mem48` gave 1.78 and 3.33 GB, which is about 43 MB a segment above a base of 1.27.
Carried to the 240 segments a part file holds that would be 11.6 GB, which cannot be right, since
twelve part files together held 14.69 GB in the run of 2026-09-19. This is the point in between.
-/

namespace PrimeCert.Mem192

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 1048576 100003 20 2048 1536 192 15

end PrimeCert.Mem192
