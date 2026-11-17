/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCert.SkipSound

/-! # A window at `10^17` with the certificate but no proved join

`ZZBP_Target1e17Skip` with `(parts / 131072) % 2` off, so `parts 3198915`. Everything else is the
same: both chunk trees four records a leaf, chunk 2048, divisors to `3.163 * 10^8`.

The phase log of the killed `ZZBP` says where its memory goes, and it is not where either of us
looked first. There is exactly one route call, at 6567 MiB, which runs to 96% of fuel and leaves
the window at 8622 MiB. The certificate then takes it to 10426 MiB, and the last line of the file
reads `before the route`, which is a stale label: the route has already run and does not run
again. Nothing is logged after that, and what follows it in the emitter is the join.

So this case asks whether the remaining 3.6 GiB is the join's proof term. If it completes, a
window at `10^17` is reachable and the join is the thing standing in the way; if it dies at the
same place, the join is innocent and the memory is somewhere the log still does not reach.

Throwaway. -/

namespace PrimeCert.SegTune.ZZCB_Target1e17NoJoin

run_sieve 316300000

set_option maxRecDepth 1000000 in
run_segment_skip_part 3198915 100000000000000001 4194304 105433333 65536 0 65536 316300000

end PrimeCert.SegTune.ZZCB_Target1e17NoJoin
