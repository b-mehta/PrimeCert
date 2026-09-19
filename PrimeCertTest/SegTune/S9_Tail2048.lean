/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The sorted run with shorter batches over the large primes

`S9_Stripes` with the batches over the primes past half the segment holding 2048 positions rather
than 3072. The 3072 was settled against the older way of marking those primes, so the three files
`S9_Tail2048`, `S9_Stripes` and `S9_Tail4096` ask the question again. -/

namespace PrimeCert.SegTune.S9_Tail2048

run_sieve 10000000

run_segment_variant 28 100000000000001 4194304 3333332 2048 10000000

end PrimeCert.SegTune.S9_Tail2048
