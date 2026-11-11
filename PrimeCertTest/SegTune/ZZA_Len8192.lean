/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The sorted band as it stands, at the tuned batch length

First of three arms. Mode 34 with every record kept and batches of 8192 positions, which is what
a sweep settled on. `ZZB_Len4096` is the same records at half that length, and `ZZC_Flagged` is
the shorter length with the out-of-window records dropped.

The three are needed rather than two because the flag costs a record bit, so it forces the shorter
length: a straight pair would move both at once and could not say which did what. Read
`ZZB` against this one for what the length costs, and `ZZC` against `ZZB` for what dropping the
records saves. A screen put that saving's ceiling at 32 percent of this band. -/

namespace PrimeCert.SegTune.ZZA_Len8192

run_sieve 10000000

run_segment_variant 34 100000000000001 4194304 333333 8192 10000000

end PrimeCert.SegTune.ZZA_Len8192
