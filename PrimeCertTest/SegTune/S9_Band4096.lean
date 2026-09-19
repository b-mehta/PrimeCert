/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The sorted run with shorter batches throughout the sorted part

`S9_Stripes` holds 16384 positions in every batch whose divisors are sorted, which covers both the
divisors striking twice and those striking three or four times. This file holds 4096 instead. The
16384 was settled when only the first of those two groups was sorted. -/

namespace PrimeCert.SegTune.S9_Band4096

run_sieve 10000000

run_segment_variant 28 100000000000001 4194304 3333332 4096 10000000

end PrimeCert.SegTune.S9_Band4096
