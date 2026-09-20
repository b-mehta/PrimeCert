/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The seed offset's two forms, over the same batches in one file

`firstLocK` used to be `(A + m * (lo / m + 1) - lo) % m` and is now `(A + m - lo % m) % m`, which
names the same offset without forming the quotient or the product. Mode 46 settles each batch of
the widest band twice, once each way, alternating which goes first, so both forms meet the same
runner, the same batches and the same cache. `run.sh` reports the old form under `batch lemmas`
and the new one under `sorted batch lemmas`. -/

namespace PrimeCert.SegTune.E1_Seed

run_sieve 10000000

run_segment_variant 46 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.E1_Seed
