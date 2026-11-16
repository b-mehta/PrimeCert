/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCert.SkipSound

/-! # A depth the route is not expected to reach

`ZZBM_JoinProved` at `10^17 + 1` with divisors to `3.163 * 10^8`, the proved design unchanged:
only the window start, the fuel and the sieve bound move. `parts 183747` as there, so the
per-window theorem is emitted and proved and `#print axioms` says whether anything was taken on
trust.

This one has no route to pair with, and that is the point rather than an omission. The two sides
are governed by different counts. The route marks every divisor, so its wide band follows the
divisor count, which `scripts/skip_rate_by_depth.py` puts at 5718065 at `10^16` and 17039277
here, three times as many. The skip design marks only the divisors that strike a live position,
which the same script puts at 199064 and 241350, a fifth of that growth. The window's live
positions sit at about 679000 at every depth, because the window width and the base depth are
both fixed, and a divisor that strikes has to take one, so the struck count has a ceiling that
does not move with the window start.

At `10^16` the route spent 704.9 s of 846.2 s kernel in the wide band against the skip design's
89.8 s. If the counts above say what they appear to, this file completes and a route at the same
depth does not finish inside any cap worth setting. If it says otherwise, the counts are not
reaching the cost and the design's advantage is narrower than `10^14` and `10^16` suggest.

Lines to read: `marked … skipped … of …` for the counts the script predicts, and `join proved:`
for the window theorem. Peak matters more than usual here: the skip design was at 7.47 GB partway
through `10^16`, so whether this fits at all is part of the answer.

The batch length is 65536, which won at `10^16` on kernel time over 8192 and 32768. Peak is the
reason it matters here rather than time: at `10^16` the same design peaked 9.92 GiB at 8192 and
6.70 GiB at 32768, and `run.sh` fails a case at 14 GB.

The `3.163 * 10^8` base sieve comes first, and on its own it is 86 to 88 processor seconds and
6.41 GiB (`S9_Sieve1e17Base`, run 43820571523).

Throwaway. -/

namespace PrimeCert.SegTune.ZZBP_Target1e17Skip

run_sieve 316300000

set_option maxRecDepth 1000000 in
run_segment_skip_part 183747 100000000000000001 4194304 105433333 65536 0 65536 316300000

#print axioms segEqAll_100000000000000001_4194304_105433333

end PrimeCert.SegTune.ZZBP_Target1e17Skip
