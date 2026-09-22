/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Two consecutive windows, struck by two walks of a batch and by one

Every window walks all 508968 divisors above 2097151 to place two strikes each, and that band is
77.2 percent of a segment's kernel while holding 4.6 percent of its strikes. Striking two windows
in one walk derives each divisor's offsets once and steps them to the second window with one
comparison and one subtraction.

Mode 47 settles each batch of that band both ways over the same two windows, alternating which
goes first. `run.sh` reports the two-walk shape under `batch lemmas` and the one-walk shape under
`sorted batch lemmas`. -/

namespace PrimeCert.SegTune.P2_Paired

run_sieve 10000000

run_segment_variant 47 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.P2_Paired
