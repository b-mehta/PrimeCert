/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The whole design at the depth it is for

`ZZAH_OneGcd1024` moved to a window at `10^16 + 1` with divisors to `10^8`: the settled shape,
chunk 1024 and one gcd, at ten times the divisors.

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
run_segment_skip_part 3523 10000000000000001 4194304 33333333 8192 0 65536 100000000

end PrimeCert.SegTune.ZZBB_Target1e16Skip
