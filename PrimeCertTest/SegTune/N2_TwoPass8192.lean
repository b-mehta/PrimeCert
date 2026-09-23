/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The twin's marking pass kept, at the batch length the parallel arms use

`S9_Par1` takes the window after each batch from that batch's own mask. This keeps the second
pass. Both cover the same segment at batch length 8192, which is the setting the runner-years
figure was measured at. -/

namespace PrimeCert.SegTune.N2_TwoPass8192

run_sieve 10000000

run_segment_variant 55 100000000000001 4194304 3333332 8192 10000000

end PrimeCert.SegTune.N2_TwoPass8192
