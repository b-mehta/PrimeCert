/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The second of two consecutive segments with the twin's marking pass kept

`N2_TwoPass8192` and this file stand to `S9_Par1` and `S9_Par2` as the kept marking pass stands to
taking the next window from the batch's own mask. Running each pair under `pair.sh` gives the
comparison in the configuration the runner-years figure was measured in. -/

namespace PrimeCert.SegTune.N3_TwoPass8192b

run_sieve 10000000

run_segment_variant 55 100000012582913 4194304 3333332 8192 10000000

end PrimeCert.SegTune.N3_TwoPass8192b
