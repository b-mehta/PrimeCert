/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The settled shape off a shallower base

`parts 52675`: `ZZBF_SweepEight` with the base built to `Wm1/128` rather than `Wm1/8`.

The base is where the marking pass's time is. Measured on the production window, it is 23.5 s of a
24 s pass, against 0.3 s for the sweep it feeds. So the pass is the base and almost nothing else,
which was not obvious until the two were timed apart.

Counted, the base is far deeper than it needs: 3510 divisors give the same strike set that 43388
do, at `10^14` and `10^15` both. But the divisor count has been the wrong unit twice today. In
records — the unit that tracked the sweep's own saving to within a point and a half — the base
only falls from 8414750 to 7424292, a ninth. A ninth of 23.5 s is the question; whether cost goes
with records here at all is part of it, since the base is marked by masks where the sweep's saving
was in sorted records, and those are different mechanisms.

Run `ZZBJ_ShallowBaseCheck` first. It is the same setting with the emitter's self-check on, and no
timing from here means anything until it says `agree true`.

Pair with `ZZBF_SweepEight`, one job, alternating, peak each. The line to read is `base built to
index … (bound …p over Wm1) in … ms`.

Throwaway. -/

namespace PrimeCert.SegTune.ZZBK_ShallowBase

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 52675 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZBK_ShallowBase
