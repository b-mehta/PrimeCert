/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # One billion-run segment through mode 15

`P0_M3` with the batches joined in a tree and the faster twin. -/

namespace PrimeCert.SegTune.P0_M15

run_segment_variant 15 100000001 262144 10573 1536

end PrimeCert.SegTune.P0_M15
