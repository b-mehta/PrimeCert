/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The eight-strike band assembled from slices of half the width

Every entry of a batch joins two bits into the state of the slice it falls in, and a batch has tens
of thousands of entries against sixty-five slices. Rewriting `stripeSort` showed that what such a
loop costs follows the width of the number being joined into rather than the number of bits set in
it, and the slice width is the one dimension of this design never swept.

This is `E9_Sorted` over the same band and the same divisors, assembled from 128 slices of 32768
bits rather than 64 of 65536. Same value, so the pair is the slice width on its own. -/

namespace PrimeCert.SegTune.E6_Half

run_sieve 10000000

run_segment_variant 40 100000000000001 4194304 3333332 3072 10000000

end PrimeCert.SegTune.E6_Half
