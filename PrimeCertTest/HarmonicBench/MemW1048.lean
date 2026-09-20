/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The same range in 24 segments of 1048576 positions, against 12 of 2097152

The width that wins on time per position and the widest a runner can hold four of are different
questions, and the sweep of one segment answers only the first: a file peaked at 1.31, 1.38 and
1.52 GB for one segment of 524288, 1048576 and 2097152 positions, but what sets how many segments
a file may carry is how that grows as they accumulate. This file and `MemW2097` cover exactly the
same 25165824 positions from the same start, so their peaks differ only in the width.
-/

namespace PrimeCert.MemW1048

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 1048576 110017 20 2048 1536 24 15

end PrimeCert.MemW1048
