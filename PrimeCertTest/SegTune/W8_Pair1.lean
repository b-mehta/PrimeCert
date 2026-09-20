/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The first of two double-width segments run at once

Throughput saturates at two files, so three and four spend memory for nothing, and the memory they
were spending is what ruled out a wider window. These two segments of 8388608 cover exactly the
range four segments of 4194304 cover, so the pair answers whether the width that was unaffordable
at four files is worth having at two. -/

namespace PrimeCert.SegTune.W8_Pair1

run_sieve 10000000

run_segment_variant 28 100000000000001 8388608 3333332 8192 10000000

end PrimeCert.SegTune.W8_Pair1
