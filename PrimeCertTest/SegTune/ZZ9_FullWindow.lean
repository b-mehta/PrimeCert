/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # One window with every divisor a run at 10^14 needs

`WA_Narrow` and the rest of `SegTune` sieve a window by the divisors up to about 10^6, a tenth of
what the top of a 10^14 range needs, because a tenth is enough to compare two routes against each
other. It is not enough to say what a run costs: the bands are reached in quite different
proportions, and the widest band, where a divisor strikes the window once or twice, holds almost
all the divisors and is barely represented at a tenth.

This case is the whole thing: 4194304 wheel positions from 10^14 + 1, sieved by every prime to
10^7, which is the square root of the range and so what the topmost window needs.

**It exists to re-anchor `scripts/fuel_by_window.py`.** That script's cost model carries an anchor
measured before the byte-array route, before the allocator settings, before clamped marking and
before the banded route, and its own header says so and says to re-anchor by repeating the
measurement on the machine a run will actually use. Until that happens every figure it prints for
how high an N is reachable is an upper bound of unknown slack.

Report kernel, processor and peak, and the band rows apart: `run.sh` splits batch lemmas, sorted
batch lemmas and wide band lemmas, which is exactly the split the script's `_SPLIT` wants. One
window alone is the right first measurement; how many fit on a runner at once is a separate
question that the peak answers. -/

namespace PrimeCert.SegTune.ZZ9_FullWindow

run_sieve 10000000

run_segment 100000000000001 4194304 3333333 8192 10000000

end PrimeCert.SegTune.ZZ9_FullWindow
