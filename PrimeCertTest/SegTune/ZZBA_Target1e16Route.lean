/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The production route at the depth the whole thing is for

`ZZH_FullWindow28` moved to a window at `10^16 + 1` sieved by every prime up to `10^8`, which is
the depth at which survivors are prime rather than merely free of small factors. Ten times the
divisors of every arm measured so far, at the same window width.

Every number in this tuning was taken at `10^14` with divisors to `10^7`. The certificate's cost
follows the number of live values, which is roughly a constant per window; the marking's follows
the number of divisors, which grows with the square root of where the window sits. Those two scale
differently, so whether the design's advantage holds at target depth is a question the measurements
so far cannot answer, and the only honest way to answer it is here.

This is expensive. It carries the whole `10^8` base sieve before the segment starts, and the
segment itself has ten times the divisors. `SegBench/E_Base1e8` is the only other case at this
depth and has never been run.

Pair with `ZZBB_Target1e16Skip`, one job, alternating, peak each.

Throwaway. -/

namespace PrimeCert.SegTune.ZZBA_Target1e16Route

run_sieve 100000000

set_option maxRecDepth 1000000 in
run_segment_variant 28 10000000000000001 4194304 33333333 8192 100000000

end PrimeCert.SegTune.ZZBA_Target1e16Route
