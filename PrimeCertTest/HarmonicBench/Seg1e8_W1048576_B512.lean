/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # A quarter sized window just above `10 ^ 8`, in batches of 512

As `Seg1e8_W1048576` with the summing batches four times shorter, to see whether the batch size
moves the memory a window needs as well as the time.
-/

namespace PrimeCert.Seg1e8QB

run_segment 100000001 1048576 10542 1536

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_segment 100000001 1048576 31627 20 512 1536

end PrimeCert.Seg1e8QB
