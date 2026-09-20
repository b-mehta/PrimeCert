/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The same eight segments, sieved and not summed (see `Split8_Full`) -/

namespace PrimeCert.Split8_Sieve

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_segment_variant 20 1000000001 1048576 33334 1536
run_segment_variant 20 1003145729 1048576 33334 1536
run_segment_variant 20 1006291457 1048576 33334 1536
run_segment_variant 20 1009437185 1048576 33334 1536
run_segment_variant 20 1012582913 1048576 33334 1536
run_segment_variant 20 1015728641 1048576 33334 1536
run_segment_variant 20 1018874369 1048576 33334 1536
run_segment_variant 20 1022020097 1048576 33334 1536

end PrimeCert.Split8_Sieve
