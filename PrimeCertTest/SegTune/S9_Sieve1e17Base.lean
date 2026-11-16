/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The base sieve a window at `10^17` would need

A window at `N` needs divisors to `sqrt N`, so every case so far has stopped at `10^8`, which is
`sqrt (10^16)`. A window at `10^17` needs `3.163 * 10^8`, and no run has ever built a base that
far. This asks whether one builds at all, and what it costs beside the `10^8` base in use today.

The question is live because the counts say the rest of the design stops growing. Across `10^16`,
`10^17` and `10^18` the divisors that strike a live position go 199064, 241350, 284720, and the
window's live positions stay near 679000, since the window width does not move with `N`. The base
is the part that does grow with the bound, so if anything decides how high `N` can go, this is a
candidate and it has never been measured.

Pair with `S8_Sieve1e8`, one job, so the two bases share a runner and the comparison is not across
machines.

Throwaway. -/

namespace PrimeCert.SegTune.S9_Sieve1e17Base

run_sieve 316300000

end PrimeCert.SegTune.S9_Sieve1e17Base
