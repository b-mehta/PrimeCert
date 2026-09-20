/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The cheap cell of the grid

The common path is a function of the width and the divisor bound together, and no series in one of
them can separate the two. What separates them is a grid, and the other session holds three bounds
at 1048576 positions while this file's neighbours hold three at 4194304. This is the fourth corner
on my side: the same width, start, form, batch length and base sieve as `C7_B1e5` and `C7_B1e6`,
with the fuel stopped at the last index below 31627, which is the bound their lowest arm uses.

Only their own ten-million case is then missing, which needs a base above it and is the expensive
one. -/

namespace PrimeCert.SegTune.C7_B31627

run_segment_variant 20 100000000000001 4194304 10542 1536 1000000

end PrimeCert.SegTune.C7_B31627
