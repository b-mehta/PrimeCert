/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Four consecutive windows, struck by four walks of a batch and by one

At two windows the one-walk shape came out 7.8 percent below the two-walk shape on this band.
Four windows derive each divisor's offsets once and step them three times, so the question is what
the saving does as the count rises.

Mode 48 settles each batch both ways over the same four windows, alternating which goes first.
`run.sh` reports the four-walk shape under `batch lemmas` and the one-walk shape under `sorted
batch lemmas`. -/

namespace PrimeCert.SegTune.P4_Quad

run_sieve 10000000

run_segment_variant 48 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.P4_Quad
