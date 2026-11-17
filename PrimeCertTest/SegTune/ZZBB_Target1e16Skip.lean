/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The whole design at the depth it is for

The settled shape moved to a window at `10^16 + 1` with divisors to `10^8`: chunk 1024, one gcd,
and the sweep starting at the eight-strike band, at ten times the divisors.

`parts 53530051` rather than the 3523 this file first carried, rather than the 52675 it carried
until both chunk trees went to four records a leaf, and rather than the 3198403 it carried until
they went to sixteen. Four a leaf took a proved window at `10^16` from 310.3 to 211.2 kernel
seconds for 1% more peak, and sixteen took another 7.6% off it for 0.87% less peak, measured four
rounds a side in one job. Sweeping the four-strike band and then
the eight-strike one each won on both kernel and processor at `10^14`, and building the base to
`Wm1/128` took the marking pass from 24.2 s to 2.44 s on top of that, so the target run should ask
about the shape that won rather than the one settled when the file was written.

What that shape gives against the production route is not yet a measured number: `parts 19907` has
only ever been run against `parts 3523`, which was itself run against the route in a different
job. Chaining the two ratios is not a measurement, and this file should not be read as carrying
one.

What this asks is whether the −15% kernel survives the move. Two things pull against each other.
The sweep's saving is in the marking, which is where the extra divisors go, so it has more to
work on. The skipped set grows with the divisors too, so the skipped product and its chain grow
with it, where the live side does not — the window still holds about the same number of primes.

Both the size of the skipped product and how much of the marking is skippable are counted by the
emitter at run time, and the log lines to read are `marked … skipped … of …` and
`skip records: … over … chunks`. Those say which way it went, whatever the headline does.

Expensive, and the same caveat as `ZZBA`: the `10^8` base sieve comes first.

Pair with `ZZBA_Target1e16Route`, one job, alternating, peak each.

Throwaway. -/

namespace PrimeCert.SegTune.ZZBB_Target1e16Skip

run_sieve 100000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 53530051 10000000000000001 4194304 33333333 65536 0 65536 100000000

end PrimeCert.SegTune.ZZBB_Target1e16Skip
