/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # One segment of 1048576 positions, for the compiled size per position

Paired with `Seg4M`, which differs only in the segment width. Comparing the two
`.olean.private` sizes says whether compiled bytes scale with the width, which decides whether a
record-sized run fits the 87 GB a runner has free.
-/

namespace PrimeCert.OleanSize.Seg1M

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1005969665 1048576 150001 20 2048 1536 1 15

end PrimeCert.OleanSize.Seg1M
