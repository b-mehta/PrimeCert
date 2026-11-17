/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCert.SkipSound

/-! # The proved window at `10^16` with a route batch of 131072

`ZZBY_Join1e16Quad` is the same at 65536, which won a sweep of 8192, 32768 and 65536 — every arm
of it at or below the setting in use, and taken before either chunk tree went to four records a
leaf or the join existed. Half this run's kernel is the route those batches make up, and the
batch length shrinks the widest band, where a divisor strikes at most twice.

Nothing above 65536 has a reading, because what a longer batch wants is peak, and peak was what
bound. At this depth it is 4.4 GB against a limit of 14.

Throwaway. -/

namespace PrimeCert.SegTune.ZZCJ_Join1e16Len131072

run_sieve 100000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 3329475 10000000000000001 4194304 33333333 131072 0 65536 100000000

#print axioms segEqAll_10000000000000001_4194304_33333333

end PrimeCert.SegTune.ZZCJ_Join1e16Len131072
