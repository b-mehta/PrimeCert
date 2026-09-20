/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # Sieved only, file 2 of four (see `Split8_Sieve`) -/

namespace PrimeCert.Split8_Sieve1

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_segment_variant 20 1025165825 1048576 33334 1536
run_segment_variant 20 1028311553 1048576 33334 1536
run_segment_variant 20 1031457281 1048576 33334 1536
run_segment_variant 20 1034603009 1048576 33334 1536
run_segment_variant 20 1037748737 1048576 33334 1536
run_segment_variant 20 1040894465 1048576 33334 1536
run_segment_variant 20 1044040193 1048576 33334 1536
run_segment_variant 20 1047185921 1048576 33334 1536

end PrimeCert.Split8_Sieve1
