/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # One of four files built together, to see what four hold at once

A file of 48 segments alone peaked at 3.33 GB and one of 192 at 9.94, which is about 46 MB a
segment. Four of these at 48 segments each should therefore hold about 13.6 GB between them, and
the record run of 2026-09-19 reported 14.69 GB across twelve larger files, which cannot both be
right. `Par1`, `Par2` and `Par3` carry the next three stretches.
-/

namespace PrimeCert.Par0

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 1048576 100003 20 2048 1536 48 15

end PrimeCert.Par0
