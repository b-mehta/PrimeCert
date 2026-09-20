/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # Sieved only, file 4 of four (see `Split8_Sieve`) -/

namespace PrimeCert.Split8_Sieve3

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_segment_variant 20 1075497473 1048576 33334 1536
run_segment_variant 20 1078643201 1048576 33334 1536
run_segment_variant 20 1081788929 1048576 33334 1536
run_segment_variant 20 1084934657 1048576 33334 1536
run_segment_variant 20 1088080385 1048576 33334 1536
run_segment_variant 20 1091226113 1048576 33334 1536
run_segment_variant 20 1094371841 1048576 33334 1536
run_segment_variant 20 1097517569 1048576 33334 1536

end PrimeCert.Split8_Sieve3
