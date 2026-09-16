/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # A quarter sized window just above `10 ^ 8`

1048576 wheel positions from `100000001`, about 3.1 million numbers, against the 4194304 of
`Seg1e8_W4194304`. The pair says how much of the memory a window uses is fixed per file and how
much grows with the window.
-/

namespace PrimeCert.Seg1e8Q

run_segment 100000001 1048576 10542 1536

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_segment 100000001 1048576 31627 20 2048 1536

end PrimeCert.Seg1e8Q
