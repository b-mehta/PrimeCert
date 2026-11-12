/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # A full-divisor window on the route the sieve runs today

Mode 28 at `ZZ9_FullWindow`'s arguments: 4194304 wheel positions from 10^14 + 1, every prime to
10^7. This is what `run_segment` emits, written as a variant so that it pairs against
`ZZJ_FullWindow82` in one job.

Pair the two with `run.sh 3`. **Both arms must be in the same job on the same box**: three fresh
boxes of the same instance type ran this file at 173 s, 177.5-184.1 s and 226 s, so a figure
carried across boxes says nothing. -/

namespace PrimeCert.SegTune.ZZH_FullWindow28

run_sieve 10000000

run_segment_variant 28 100000000000001 4194304 3333333 8192 10000000

end PrimeCert.SegTune.ZZH_FullWindow28
