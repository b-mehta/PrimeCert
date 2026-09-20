/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # Sieved only, file 3 of four (see `Split8_Sieve`) -/

namespace PrimeCert.Split8_Sieve2

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_segment_variant 20 1050331649 1048576 33334 1536
run_segment_variant 20 1053477377 1048576 33334 1536
run_segment_variant 20 1056623105 1048576 33334 1536
run_segment_variant 20 1059768833 1048576 33334 1536
run_segment_variant 20 1062914561 1048576 33334 1536
run_segment_variant 20 1066060289 1048576 33334 1536
run_segment_variant 20 1069206017 1048576 33334 1536
run_segment_variant 20 1072351745 1048576 33334 1536

end PrimeCert.Split8_Sieve2
