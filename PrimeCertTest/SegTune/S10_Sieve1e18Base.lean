/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The base sieve a window at `10^18` would need

A window at `N` needs divisors to `sqrt N`, so `10^18` needs `10^9`, against the `3.163 * 10^8`
that `10^17` uses and the `10^8` that `10^16` does.

This is the cheapest thing that could rule `10^18` out. The base alone was 2.00 GiB at `10^8` and
6.41 GiB at `3.163 * 10^8`, and a proved window at `10^17` finishes at 10.53 GiB with 2.82 GiB
under `run.sh`'s limit. If the `10^9` base does not fit on its own then nothing above it will, and
that is worth one run to learn rather than inferring from the two figures below it.

Pair with `S8_Sieve1e8` and `S9_Sieve1e17Base`, whose numbers it extends.

Throwaway. -/

namespace PrimeCert.SegTune.S10_Sieve1e18Base

run_sieve 1000000000

end PrimeCert.SegTune.S10_Sieve1e18Base
