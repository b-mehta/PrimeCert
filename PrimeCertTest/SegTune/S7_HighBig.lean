/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt14

/-! # `S7_High` with a base five and a half times larger, nothing else moved

The sieve session measured a tenfold base costing about 5 percent of kernel time at 4194304
positions, on arms whose divisors, batches and emitted statements are the same, and 0.06 s of
that 5.3 falls in the slice lemmas that are the only statements mentioning the base at all. This
file pairs against `S7_High` to say whether that cost is a constant or grows with the segment: the
same fuel 333334, the same 1048576 positions, the same start, the same batch length, with the base
at eleven million instead of two.

The base cannot be moved at the largest bound instead, which would have matched their tenfold more
closely: a base must cover the bound it supplies, so fuel 3333332 admits no base below ten million
and the only pair available there is eleven against thirty-two million.
-/

namespace PrimeCert.SegTune.S7_HighBig

run_segment_variant 20 1005969665 1048576 333334 1536 11000000

end PrimeCert.SegTune.S7_HighBig
