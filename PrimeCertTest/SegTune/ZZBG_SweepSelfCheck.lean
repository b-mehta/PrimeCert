/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Does the sweep still get the window right a band lower?

`parts 8202` and `parts 16394`: the sweep starting at the four-strike and the eight-strike band,
with the emitter's own self-check on and nothing else emitted.

I argued that moving the sweep down a band keeps it sound — a divisor striking nothing live in the
base strikes nothing in the finished window, and a base with more live bits than the window can
only make a divisor look like a striker, never the reverse — and then shipped the knob without
having anything check it. The self-check is exactly the thing that would: it rebuilds the window
from the marked subset alone and refuses to emit if that differs from marking by every divisor.

So this is a correctness arm, not a timing one. `pbase 2` turns the check on and the gcds off, and
the low digits stop below the record certificate, so each run is the marking pass, the sweep, the
check and the route. A wrong skip set fails here with a clear message rather than silently
certifying a window that was never built.

Worth running before either `ZZBE_SweepFour` or `ZZBF_SweepEight` is believed, whatever their
timings say. The check has not run at all since the base became the small band alone, so it is
also the first time that change is tested rather than argued.

One setting a file. Both were in this one to save a build, which cost more than it saved: the
emitter's log is truncated at the start of each run, so the second command overwrote the first's
`agree` line and the run had to be done again to read it. `ZZBH_SweepEightCheck` is the other
setting.

Timings here mean nothing: the check is a second full marking pass that production never does.

Throwaway. -/

namespace PrimeCert.SegTune.ZZBG_SweepSelfCheck

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 8202 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZBG_SweepSelfCheck
