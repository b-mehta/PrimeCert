/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The four-strike band, settled by records and by a tree with leaves of 262144 bits

The divisors striking the window at most four times hold 2.21 percent of a segment's strikes. The
run settles them today by sorting each divisor's strikes into records.

Mode 51 settles each batch of that band both ways, alternating which goes first. `run.sh` reports
the records under `batch lemmas` and the tree under `sorted batch lemmas`. -/

namespace PrimeCert.SegTune.M4_Mid

run_sieve 10000000

run_segment_variant 51 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.M4_Mid
