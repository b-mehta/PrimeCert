/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt14

/-! # The last corner of the grid: the sieve session's bound at my width

My three arms run at 1048576 positions with bounds 31627, 110017 and 1000003; theirs run at
4194304 with 31627, 1e5, 1e6 and 1e7. The one cell neither series holds is their largest bound at
my width, and without it no pair anywhere separates the width from the bound at a fixed divisor
count. Fuel 3333332 stops at 9999997, the same divisors their `S7_Sched` uses.

The base here is eleven million rather than the two million my other three read. That would have
mattered until they measured it: a tenfold base with everything else held moved their residual by
0.6 percent, so the base is not in the quantity this grid is made of. It did move their kernel
time by about 5 percent, which is why this file is not also used for a kernel comparison.
-/

namespace PrimeCert.SegTune.S7_Max

run_segment_variant 20 1005969665 1048576 3333332 1536 11000000

end PrimeCert.SegTune.S7_Max
